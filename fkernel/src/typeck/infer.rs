//! Infers types of expressions.

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Span};
use fnodes::{basic_nodes::Provenance, expr::*, universe::*};

use crate::expr::{
    abstract_pi, has_free_variables, instantiate, instantiate_universe_parameters, ExprPrinter,
};

use super::{defeq::definitionally_equal_core, env::Environment, whnf::to_weak_head_normal_form};

/// Infers the type of an expression. Invoke with a closed expression.
/// If `check` is true, we also perform some type checking, but the return value is not changed.
/// If the expression is type-correct, the return value is the expression's type, and further,
/// if `check` is true and the return value is not an error, the expression is type-correct.
pub fn infer_type(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    e: &Expr,
    check: bool,
) -> Dr<Expr> {
    if has_free_variables(e) {
        return Dr::fail(
            Report::new(ReportKind::Error, env.source, e.provenance.span().start).with_label(
                Label::new(env.source, e.provenance.span(), LabelType::Error).with_message(
                    "could not infer type of expression because it had free variables",
                ),
            ),
        );
    }

    match infer_type_core(env, meta_gen, e, check) {
        Ok(val) => Dr::ok(val),
        Err(err) => Dr::fail(err(Report::new(
            ReportKind::Error,
            env.source,
            e.provenance.span().start,
        ))),
    }
}

pub(crate) fn infer_type_core<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    e: &Expr,
    check: bool,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    match &e.contents {
        ExprContents::Bound(_) => unreachable!("expression should not have free variables"),
        ExprContents::Inst(inst) => infer_type_inst(env, e.provenance.span(), check, inst),
        ExprContents::Let(inner) => {
            infer_type_let(env, meta_gen, e.provenance.span(), check, inner)
        }
        ExprContents::Lambda(lambda) => infer_type_lambda(env, meta_gen, check, lambda),
        ExprContents::Pi(pi) => infer_type_pi(env, meta_gen, e.provenance.span(), check, pi),
        ExprContents::Apply(apply) => {
            infer_type_apply(env, meta_gen, e.provenance.span(), check, apply)
        }
        ExprContents::Sort(sort) => infer_type_sort(env, &e.provenance, check, sort),
        ExprContents::Metavariable(var) => Ok(*var.ty.clone()),
        ExprContents::LocalConstant(local) => Ok(*local.metavariable.ty.clone()),
    }
}

fn infer_type_inst<'a>(
    env: &'a Environment,
    span: Span,
    check: bool,
    inst: &Inst,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    let path = inst.name.to_path(env.db.up());
    match env.definitions.get(&path) {
        Some(def) => {
            if def.def().contents.universe_params.len() == inst.universes.len() {
                let mut e = def.def().contents.ty.clone();
                if check {
                    for u in &inst.universes {
                        check_valid_universe(env, u)?;
                    }
                }
                instantiate_universe_parameters(
                    &mut e,
                    &def.def().contents.universe_params,
                    &inst.universes,
                );
                Ok(e)
            } else {
                let inst = inst.clone();
                Err(Box::new(move |report| {
                    report
                        .with_message(
                            "incorrect number of universe parameters were supplied to definition",
                        )
                        .with_label(Label::new(env.source, span, LabelType::Error).with_message(
                            format!(
                                "definition {} has {} universe parameters, but {} were supplied",
                                path.display(env.db.up()),
                                def.def().contents.universe_params.len(),
                                inst.universes.len()
                            ),
                        ))
                        .with_label(
                            Label::new(
                                def.def().provenance.source().unwrap_or(env.source),
                                def.def().provenance.span(),
                                LabelType::Note,
                            )
                            .with_message(format!("{} defined here", path.display(env.db.up()),)),
                        )
                }))
            }
        }
        None => Err(Box::new(move |report| {
            report
                .with_label(Label::new(env.source, span, LabelType::Error))
                .with_message(format!(
                    "definition {} could not be found in the environment",
                    path.display(env.db.up())
                ))
                .with_note(
                    env.definitions
                        .keys()
                        .map(|def| format!("\n      \u{2022} {}", def.display(env.db.up())))
                        .fold("environment contains:".to_string(), |l, r| l + &r),
                )
        })),
    }
}

fn infer_type_let<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    span: Span,
    check: bool,
    inner: &Let,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if check {
        // The type of the value to assign must be a type.
        // That is, its type must be a sort.
        let let_type_type = infer_type_core(env, meta_gen, &inner.to_assign_ty, check)?;
        as_sort_core(env, inner.to_assign_ty.provenance.span(), let_type_type)?;

        // Infer the type of the value to substitute.
        let let_value_type = infer_type_core(env, meta_gen, &inner.to_assign, check)?;

        // The value that we assign must have type definitionally equal to the `to_assign_ty`.
        if !definitionally_equal_core(env, meta_gen, &let_value_type, &inner.to_assign_ty)? {
            let inner = inner.clone();
            return Err(Box::new(move |report| {
                let mut printer = ExprPrinter::new(env.db);
                report
                    .with_label(Label::new(env.source, span, LabelType::Error))
                    .with_message(format!(
                        "argument to let-expression {} had type {}, but was expected to have type {}",
                        printer.print(&inner.to_assign),
                        printer.print(&let_value_type),
                        printer.print(&inner.to_assign_ty),
                    ))
            }));
        }
    }

    let mut body = *inner.body.clone();
    instantiate(&mut body, &inner.to_assign);
    infer_type_core(env, meta_gen, &body, check)
}

fn infer_type_lambda<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    check: bool,
    lambda: &Lambda,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if check {
        // The argument type must be a type.
        let argument_type_type = infer_type_core(env, meta_gen, &lambda.parameter_ty, check)?;
        as_sort_core(
            env,
            lambda.parameter_ty.provenance.span(),
            argument_type_type,
        )?;
    }
    // Infer the return type of the lambda by first instantiating the parameter then inferring the resulting type.
    let new_local = lambda.generate_local(meta_gen);
    let mut body = *lambda.result.clone();
    instantiate(
        &mut body,
        &Expr::new_in_sexpr(
            env.source,
            lambda.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    let return_type = infer_type_core(env, meta_gen, &body, check)?;
    Ok(Expr::new_with_provenance(
        &lambda.parameter_ty.provenance,
        ExprContents::Pi(abstract_pi(new_local, return_type)),
    ))
}

fn infer_type_pi<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    span: Span,
    check: bool,
    pi: &Pi,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    let parameter_type = infer_type_core(env, meta_gen, &pi.parameter_ty, check)?;
    let domain_type = as_sort_core(env, span.clone(), parameter_type)?;
    let mut body = *pi.result.clone();
    instantiate(
        &mut body,
        &Expr::new_in_sexpr(
            env.source,
            pi.parameter_name.provenance.span(),
            ExprContents::LocalConstant(pi.generate_local(meta_gen)),
        ),
    );
    let return_type = as_sort_core(env, span, infer_type_core(env, meta_gen, &body, check)?)?;
    Ok(Expr::new_with_provenance(
        &pi.parameter_ty.provenance,
        ExprContents::Sort(Sort(Universe::new_with_provenance(
            &pi.parameter_ty.provenance,
            UniverseContents::UniverseImpredicativeMax(UniverseImpredicativeMax {
                left: Box::new(domain_type.0),
                right: Box::new(return_type.0),
            }),
        ))),
    ))
}

fn infer_type_apply<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    span: Span,
    check: bool,
    apply: &Apply,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    let function_type = as_pi(
        env,
        span,
        infer_type_core(env, meta_gen, &apply.function, check)?,
    )?;
    let argument_type = infer_type_core(env, meta_gen, &apply.argument, check)?;
    if check
        && !definitionally_equal_core(env, meta_gen, &argument_type, &function_type.parameter_ty)?
    {
        let func_span = apply.function.provenance.span();
        let arg_span = apply.argument.provenance.span();
        return Err(Box::new(move |report| {
            let mut printer = ExprPrinter::new(env.db);
            report
                .with_message(format!(
                    "function of type\n\t{}\ncannot be applied to value of type\n\t{}\nthe function expects a parameter of type\n\t{}",
                    printer.print(&Expr::new_synthetic(ExprContents::Pi(
                        function_type.clone()
                    ))),
                    printer.print(&argument_type),
                    printer.print(&function_type.parameter_ty)
                ))
                .with_label(
                    Label::new(env.source, func_span, LabelType::Error).with_message("function"),
                )
                .with_label(
                    Label::new(env.source, arg_span, LabelType::Error).with_message("argument"),
                )
        }));
    }
    let mut return_type = *function_type.result;
    instantiate(&mut return_type, &apply.argument);
    Ok(return_type)
}

fn infer_type_sort<'a>(
    env: &'a Environment,
    provenance: &Provenance,
    check: bool,
    sort: &Sort,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if check {
        check_valid_universe(env, &sort.0)?;
    }
    Ok(Expr::new_with_provenance(
        provenance,
        ExprContents::Sort(Sort(Universe::new_with_provenance(
            provenance,
            UniverseContents::UniverseSucc(UniverseSucc(Box::new(sort.0.clone()))),
        ))),
    ))
}

/// Expands the given expression until it is a [`Sort`].
/// If the expression was not a sort, returns [`Err`].
fn as_sort_core<'a>(
    env: &'a Environment,
    span: Span,
    mut e: Expr,
) -> Result<Sort, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if let ExprContents::Sort(sort) = e.contents {
        Ok(sort)
    } else {
        to_weak_head_normal_form(env, &mut e);
        if let ExprContents::Sort(sort) = e.contents {
            Ok(sort)
        } else {
            Err(Box::new(move |report| {
                let mut printer = ExprPrinter::new(env.db);
                report
                    .with_label(Label::new(env.source, span, LabelType::Error))
                    .with_message(format!(
                        "expression was expected to be a sort, but was deduced to be {}",
                        printer.print(&e),
                    ))
            }))
        }
    }
}

/// Expands the given expression until it is a [`Sort`].
/// If the expression was not a sort, returns a failed [`Dr`].
pub fn as_sort(env: &Environment, e: Expr) -> Dr<Sort> {
    let provenance = e.provenance.clone();
    match as_sort_core(env, provenance.span(), e) {
        Ok(sort) => Dr::ok(sort),
        Err(err) => Dr::fail(err(Report::new(
            ReportKind::Error,
            env.source,
            provenance.span().start,
        ))),
    }
}

/// Expands the given expression until it is a [`Pi`].
/// If the expression was not a function type, returns [`Err`].
fn as_pi<'a>(
    env: &'a Environment,
    span: Span,
    mut e: Expr,
) -> Result<Pi, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if let ExprContents::Pi(pi) = e.contents {
        Ok(pi)
    } else {
        to_weak_head_normal_form(env, &mut e);
        if let ExprContents::Pi(pi) = e.contents {
            Ok(pi)
        } else {
            Err(Box::new(move |report| {
                let mut printer = ExprPrinter::new(env.db);
                report
                    .with_label(Label::new(env.source, span, LabelType::Error))
                    .with_message(format!(
                        "expression was expected to be a function type, but was deduced to be {}",
                        printer.print(&e),
                    ))
            }))
        }
    }
}

/// Check that this universe contains no uninitialised universe variables and no metauniverses.
fn check_valid_universe<'a>(
    env: &'a Environment,
    u: &Universe,
) -> Result<(), Box<dyn FnOnce(Report) -> Report + 'a>> {
    match &u.contents {
        UniverseContents::UniverseZero => Ok(()),
        UniverseContents::UniverseVariable(var) => {
            // Check that this universe variable was given as a universe parameter.
            if env
                .universe_variables
                .iter()
                .any(|name| var.0 == name.contents)
            {
                Ok(())
            } else {
                let span = u.provenance.span();
                let parameter_name = env.db.lookup_intern_string_data(var.0);
                Err(Box::new(move |report| {
                    report
                        .with_message("could not find universe parameter")
                        .with_label(Label::new(env.source, span, LabelType::Error).with_message(
                            format!(
                                "universe parameter {} could not be found in the environment",
                                parameter_name,
                            ),
                        ))
                }))
            }
        }
        UniverseContents::UniverseSucc(inner) => check_valid_universe(env, &inner.0),
        UniverseContents::UniverseMax(max) => {
            check_valid_universe(env, &max.left)?;
            check_valid_universe(env, &max.right)
        }
        UniverseContents::UniverseImpredicativeMax(imax) => {
            check_valid_universe(env, &imax.left)?;
            check_valid_universe(env, &imax.right)
        }
        UniverseContents::Metauniverse(_) => Err(todo!()),
    }
}
