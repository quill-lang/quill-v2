use std::cell::Cell;

use fcommon::{Dr, Label, LabelType, Report, ReportKind};
use fnodes::{
    basic_nodes::{Name, QualifiedName},
    definition::{Definition, DefinitionContents},
    expr::{Expr, ExprContents, Inst, MetavariableGenerator, Pi, Sort},
    inductive::{Inductive, IntroRule},
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::{
        apply_args, closed, destructure_as_nary_application, find_constant, has_free_variables,
        instantiate, ExprPrinter,
    },
    typeck::{
        self, as_sort, check_no_local_or_metavariable, definitionally_equal, infer_type,
        to_weak_head_normal_form, CertifiedDefinition, Environment,
    },
    universe::{is_nonzero, is_zero, normalise_universe, universe_at_most},
};

use super::check::PartialInductiveInformation;

/// Verifies that an introduction rule for an inductive type is valid and can be added to the environment.
/// We require that
/// - all intro rules start with the same global parameters,
/// - the type of all arguments live in universes at most the level of the corresponding data type,
/// - occurences of the inductive data type inside this introduction rule occur strictly positively,
/// - the rule is type correct.
/// Then, returns a certified definition (with empty body) representing the intro rule.
pub fn check_intro_rule(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    intro_rule: &IntroRule,
    info: &PartialInductiveInformation,
) -> Dr<CertifiedDefinition> {
    check_intro_rule_core(env, meta_gen, ind, intro_rule, info).bind(|()| {
        // The intro rule was valid, so we can now define and certify it.
        typeck::check(
            env,
            &Definition {
                provenance: intro_rule.name.provenance.clone(),
                contents: DefinitionContents {
                    name: intro_rule.name.clone(),
                    universe_params: ind.contents.universe_params.clone(),
                    ty: intro_rule.ty.clone(),
                    expr: None,
                },
            },
        )
    })
}

fn check_intro_rule_core(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    intro_rule: &IntroRule,
    info: &PartialInductiveInformation,
) -> Dr<()> {
    check_no_local_or_metavariable(env, &intro_rule.ty).bind(|()| {
        // Ensure that `ind.contents.ty` is type correct.
        infer_type(env, meta_gen, &ind.contents.ty, true).bind(|_| {
            // Unpack the intro rule's type as a sequence of `Pi` abstractions.
            let mut ty = intro_rule.ty.clone();
            let mut parameter_index = 0;
            let mut found_recursive_argument = false;
            let result = loop {
                if let ExprContents::Pi(pi) = ty.contents {
                    if parameter_index < ind.contents.global_params {
                        // This parameter is a global parameter.
                        // It must be definitionally equal to the `i`th global parameter of the inductive.
                        let defeq_result = definitionally_equal(
                            env,
                            meta_gen,
                            &*pi.parameter_ty,
                            &*info.global_params[parameter_index as usize].metavariable.ty,
                        );
                        match defeq_result.value() {
                            Some(true) => {}
                            _ => break defeq_result.map(|_| todo!()),
                        }
                        ty = *pi.result;
                        instantiate(
                            &mut ty,
                            &Expr::new_synthetic(ExprContents::LocalConstant(
                                info.global_params[parameter_index as usize].clone(),
                            )),
                        );
                    } else {
                        // This is an index parameter.
                        let new_ty = check_index_parameter(
                            env,
                            meta_gen,
                            intro_rule,
                            ind,
                            info,
                            pi,
                            &mut found_recursive_argument,
                            parameter_index,
                        );
                        if let Some(new_ty) = new_ty.value() {
                            ty = new_ty.clone();
                        } else {
                            break new_ty.map(|_| todo!());
                        }
                    }

                    parameter_index += 1;
                } else {
                    break Dr::ok(ty);
                }
            };
            result.bind(|ty| {
                is_valid_inductive_application(env, meta_gen, &ty, info).bind(|result| {
                    if result {
                        Dr::ok(())
                    } else {
                        let mut printer = ExprPrinter::new(env.db);
                        Dr::fail(
                            Report::new(ReportKind::Error, env.source, ty.provenance.span().start)
                                .with_message(format!(
                                    "invalid return type for introduction rule {}",
                                    env.db.lookup_intern_string_data(intro_rule.name.contents)
                                ))
                                .with_label(
                                    Label::new(env.source, ty.provenance.span(), LabelType::Error)
                                        .with_message(format!(
                                            "return type was {}",
                                            printer.print(&ty)
                                        )),
                                ),
                        )
                    }
                })
            })
        })
    })
}

fn check_index_parameter(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    intro_rule: &IntroRule,
    ind: &Inductive,
    info: &PartialInductiveInformation,
    pi: Pi,
    found_recursive_argument: &mut bool,
    parameter_index: u32,
) -> Dr<Expr> {
    let local = pi.generate_local(meta_gen);
    infer_type(env, meta_gen, &*pi.parameter_ty, true).bind(|sort| {
        as_sort(env, sort).bind(|sort| {
            // The type of the type of this index parameter is allowed if
            // - its level is at most the level of the inductive data type being declared, or
            // - the inductive data type has sort 0.
            if !is_zero(&info.sort.0) {
                if !universe_at_most(sort.0.clone(), info.sort.0.clone()) {
                    let mut print = ExprPrinter::new(env.db);
                    tracing::debug!("LEFT: {}", print.print_universe(&sort.0));
                    tracing::debug!("RIGHT: {}", print.print_universe(&info.sort.0));
                    let mut l = sort.0.clone();
                    normalise_universe(&mut l);
                    let mut r = info.sort.0.clone();
                    normalise_universe(&mut r);
                    tracing::debug!("NEW LEFT: {}", print.print_universe(&sort.0));
                    tracing::debug!("NEW RIGHT: {}", print.print_universe(&info.sort.0));
                    return Dr::fail(
                        Report::new(
                            ReportKind::Error,
                            env.source,
                            pi.result.provenance.span().start,
                        )
                        .with_message("this is an invalid argument for this intro rule")
                        .with_label(Label::new(env.source, pi.result.provenance.span(), LabelType::Error)
                            .with_message(format!(
                                "this type had sort {}, which could exceed the inductive's sort {}",
                                print.print(&Expr::new_synthetic(ExprContents::Sort(sort))),
                                print.print(&Expr::new_synthetic(ExprContents::Sort(info.sort.clone()))),
                            )))
                        .with_label(Label::new(env.source, ind.contents.ty.provenance.span().clone(), LabelType::Note)
                            .with_message(format!(
                                "error was emitted because the resulting inductive has sort {}, which may be in a higher universe than {}",
                                print.print(&Expr::new_synthetic(ExprContents::Sort(info.sort.clone()))),
                                print.print(&Expr::new_synthetic(ExprContents::Sort(Sort(Universe::new_synthetic(UniverseContents::UniverseZero))))),
                            ))),
                    );
                }
            }

            // Check that the inductive data type occurs strictly positively.
            check_positivity(
                env,
                meta_gen,
                *pi.parameter_ty.clone(),
                intro_rule,
                info,
                parameter_index,
            )
            .bind(|()| {
                is_recursive_argument(env, meta_gen, *pi.parameter_ty, info).bind(|is_recursive| {
                    if is_recursive {
                        *found_recursive_argument = true;
                    }
                    if *found_recursive_argument {
                        if has_free_variables(&pi.result) {
                            // This is an invalid occurrence of a recursive argument
                            // because the body of the functional type depends on it.
                            let mut print = ExprPrinter::new(env.db);
                            Dr::fail(
                                Report::new(
                                    ReportKind::Error,
                                    env.source,
                                    pi.result.provenance.span().start,
                                )
                                .with_message("this is an invalid occurrence of a recursive argument, because the body of the functional type depends on it")
                                .with_label(Label::new(env.source, pi.result.provenance.span(), LabelType::Error)
                                    .with_message(format!("this type was {}, which contains free variables", print.print(&pi.result)))),
                            )
                        } else {
                            Dr::ok(*pi.result)
                        }
                    } else {
                        let mut result = *pi.result;
                        instantiate(
                            &mut result,
                            &Expr::new_synthetic(ExprContents::LocalConstant(local.clone())),
                        );
                        Dr::ok(result)
                    }
                })
            })
        })
    })
}

/// Check that the inductive data type being declared occurs strictly positively in the given expression.
fn check_positivity(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    mut e: Expr,
    intro_rule: &IntroRule,
    info: &PartialInductiveInformation,
    parameter_index: u32,
) -> Dr<()> {
    let segments = info
        .inst
        .name
        .segments
        .iter()
        .map(|name| name.contents)
        .collect::<Vec<_>>();
    to_weak_head_normal_form(env, &mut e);
    if find_constant(&e, &segments).is_some() {
        // This is a recursive argument, so we need to check for positivity.
        if let ExprContents::Pi(pi) = e.contents {
            if let Some(value) = find_constant(&*pi.parameter_ty, &segments) {
                // This is a non-positive occurence of the inductive type being declared.
                Dr::fail(todo!())
            } else {
                let local = pi.generate_local(meta_gen);
                let mut result = *pi.result;
                instantiate(
                    &mut result,
                    &Expr::new_synthetic(ExprContents::LocalConstant(local)),
                );
                check_positivity(env, meta_gen, result, intro_rule, info, parameter_index)
            }
        } else {
            is_valid_inductive_application(env, meta_gen, &e, info).bind(|result| {
                if result {
                    // This is a valid recursive inductive application.
                    Dr::ok(())
                } else {
                    // This is an invalid inductive application.
                    Dr::fail(todo!())
                }
            })
        }
    } else {
        Dr::ok(())
    }
}

/// Returns true if the expression is a term of the form `(I As t)` where `I` is the inductive being
/// defined, `As` are the global parameters, and `I` does not occur in the indices `t`.
pub(in crate::inductive) fn is_valid_inductive_application(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    e: &Expr,
    info: &PartialInductiveInformation,
) -> Dr<bool> {
    let (function, arguments) = destructure_as_nary_application(e);
    definitionally_equal(
        env,
        meta_gen,
        function,
        &Expr::new_synthetic(ExprContents::Inst(info.inst.clone())),
    )
    .map(|defeq| {
        if !defeq {
            // The application was not of the form `(I ...)`.
            return false;
        }
        if arguments.len() != info.global_params.len() + info.index_params.len() {
            // The application was of the form `(I ...)`, but an incorrect number of parameters to the inductive were supplied.
            return false;
        }
        let segments = info
            .inst
            .name
            .segments
            .iter()
            .map(|name| name.contents)
            .collect::<Vec<_>>();
        arguments
            .iter()
            .zip(&info.global_params)
            .all(|(left, right)| {
                left.eq_ignoring_provenance(&Expr::new_synthetic(ExprContents::LocalConstant(
                    right.clone(),
                )))
            })
            && arguments
                .iter()
                .skip(info.global_params.len())
                .all(|arg| find_constant(arg, &segments).is_none())
    })
}

/// Returns true if the expression is a recursive argument.
pub(in crate::inductive) fn is_recursive_argument(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    mut e: Expr,
    info: &PartialInductiveInformation,
) -> Dr<bool> {
    to_weak_head_normal_form(env, &mut e);
    while let ExprContents::Pi(pi) = e.contents {
        let local = pi.generate_local(meta_gen);
        e = *pi.result;
        instantiate(
            &mut e,
            &Expr::new_synthetic(ExprContents::LocalConstant(local)),
        );
        to_weak_head_normal_form(env, &mut e);
    }
    is_valid_inductive_application(env, meta_gen, &e, info)
}
