//! Infers types of expressions.

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Span};
use fnodes::{expr::*, universe::*};

use crate::expr::{
    abstract_pi, closed, has_free_variables, instantiate, instantiate_universe_parameters,
};

use super::{defeq::definitionally_equal, env::Environment, whnf::to_weak_head_normal_form};

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

fn infer_type_core<'a>(
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
        ExprContents::Lambda(lambda) => {
            infer_type_lambda(env, meta_gen, e.provenance.span(), check, lambda)
        }
        ExprContents::Pi(_) => todo!(),
        ExprContents::Apply(_) => todo!(),
        ExprContents::Sort(_) => todo!(),
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
            if def.contents.universe_params.len() == inst.universes.len() {
                let mut e = def.contents.ty.clone();
                instantiate_universe_parameters(
                    &mut e,
                    &def.contents.universe_params,
                    &inst.universes,
                );
                Ok(e)
            } else {
                let inst = inst.clone();
                Err(Box::new(move |report| {
                    report
                        .with_label(Label::new(env.source, span, LabelType::Error).with_message(
                            format!(
                                "definition {} has {} universe parameters, but {} were supplied",
                                path.display(env.db.up()),
                                def.contents.universe_params.len(),
                                inst.universes.len()
                            ),
                        ))
                        .with_label(
                            Label::new(
                                def.provenance.source().unwrap_or(env.source),
                                def.provenance.span(),
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
        let let_type_type = infer_type_core(env, meta_gen, &*inner.to_assign_ty, check)?;
        as_sort(env, inner.to_assign_ty.provenance.span(), let_type_type)?;

        // Infer the type of the value to substitute.
        let let_value_type = infer_type_core(env, meta_gen, &*inner.to_assign, check)?;

        // The value that we assign must have type definitionally equal to the `to_assign_ty`.
        if !definitionally_equal(&let_value_type, &*inner.to_assign_ty) {
            let inner = inner.clone();
            return Err(Box::new(move |report| {
                let mut printer = ExprPrinter::new(env.db);
                report
                    .with_label(Label::new(env.source, span, LabelType::Error))
                    .with_message(format!(
                        "argument to let-expression {} had type {}, but was expected to have type {}",
                        printer.print(&*inner.to_assign),
                        printer.print(&let_value_type),
                        printer.print(&*inner.to_assign_ty),
                    ))
            }));
        }
    }

    let mut body = *inner.body.clone();
    instantiate(&mut body, &*inner.to_assign);
    infer_type_core(env, meta_gen, &body, check)
}

fn infer_type_lambda<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    span: Span,
    check: bool,
    lambda: &Lambda,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if check {
        // The argument type must be a type.
        let argument_type_type = infer_type_core(env, meta_gen, &*lambda.parameter_ty, check)?;
        as_sort(
            env,
            lambda.parameter_ty.provenance.span(),
            argument_type_type,
        )?;
    }
    // Infer the return type of the lambda by first instantiating the parameter then inferring the resulting type.
    let mut body = *lambda.result.clone();
    let new_local = LocalConstant {
        name: lambda.parameter_name.clone(),
        metavariable: meta_gen.gen(*lambda.parameter_ty.clone()),
        binder_annotation: lambda.binder_annotation,
    };
    instantiate(
        &mut body,
        &Expr::new_in_sexpr(
            env.source,
            lambda.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    let mut return_type = infer_type_core(env, meta_gen, &body, check)?;
    Ok(Expr::new_with_provenance(
        &lambda.parameter_ty.provenance,
        ExprContents::Pi(abstract_pi(new_local, return_type)),
    ))
}

/// Expands the given expression until it is a `Sort`.
/// If the expression was not a sort, returns `Err`.
fn as_sort<'a>(
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
