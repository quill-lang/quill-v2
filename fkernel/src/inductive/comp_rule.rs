use fcommon::Dr;
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::*,
    inductive::{Inductive, IntroRule},
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::{abstract_nary_lambda, apply_args, instantiate, ExprPrinter},
    typeck::{self, definitionally_equal, to_weak_head_normal_form, Environment},
};

use super::{
    check::PartialInductiveInformation,
    recursor_info::{get_indices, split_intro_rule_type, RecursorInfo},
};

/// Creates the computation rules for computing outputs of the recursor.
pub fn generate_computation_rules(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
    rec_info: &RecursorInfo,
) -> Dr<Vec<ComputationRule>> {
    Dr::sequence(
        ind.contents
            .intro_rules
            .iter()
            .zip(&rec_info.minor_premises)
            .map(|(intro_rule, minor_premise)| {
                generate_computation_rule(
                    env,
                    meta_gen,
                    ind,
                    intro_rule,
                    minor_premise,
                    info,
                    rec_info,
                )
            }),
    )
    .map(|rules| {
        let mut print = ExprPrinter::new(env.db);
        for rule in &rules {
            tracing::debug!(
                "computation rule has value {} => {}",
                print.print(&rule.eliminator_application),
                print.print(&rule.minor_premise_application),
            );
        }
        rules
    })
}

/// A computation rule converts an application of an eliminator into an application of one of the minor premises to the eliminator.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ComputationRule {
    pub eliminator_application: Expr,
    pub minor_premise_application: Expr,
}

fn generate_computation_rule(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    intro_rule: &IntroRule,
    minor_premise: &LocalConstant,
    info: &PartialInductiveInformation,
    rec_info: &RecursorInfo,
) -> Dr<ComputationRule> {
    let eliminator_name = env.db.intern_string_data(format!(
        "{}.rec",
        env.db.lookup_intern_string_data(ind.contents.name.contents)
    ));

    let eliminator = Expr::new_synthetic(ExprContents::Inst(Inst {
        name: QualifiedName {
            provenance: Provenance::Synthetic,
            segments: env
                .db
                .lookup_intern_path_data(env.source.path)
                .0
                .into_iter()
                .chain(std::iter::once(eliminator_name))
                .map(|s| Name {
                    provenance: Provenance::Synthetic,
                    contents: s,
                })
                .collect(),
        },
        universes: ind
            .contents
            .universe_params
            .iter()
            .map(|univ| {
                Universe::new_with_provenance(
                    &univ.provenance,
                    UniverseContents::UniverseVariable(UniverseVariable(univ.contents)),
                )
            })
            .collect(),
    }));

    let intro_rule_expr = Expr::new_synthetic(ExprContents::Inst(Inst {
        name: QualifiedName {
            provenance: Provenance::Synthetic,
            segments: env
                .db
                .lookup_intern_path_data(env.source.path)
                .0
                .into_iter()
                .map(|s| Name {
                    provenance: Provenance::Synthetic,
                    contents: s,
                })
                .chain(std::iter::once(intro_rule.name.clone()))
                .collect(),
        },
        universes: ind
            .contents
            .universe_params
            .iter()
            .map(|univ| {
                Universe::new_with_provenance(
                    &univ.provenance,
                    UniverseContents::UniverseVariable(UniverseVariable(univ.contents)),
                )
            })
            .collect(),
    }));

    split_intro_rule_type(env, meta_gen, ind, info, intro_rule.ty.clone()).bind(|split_result| {
        Dr::sequence(split_result.recursive.iter().map(|arg| {
            let mut local_ty = *arg.metavariable.ty.clone();
            to_weak_head_normal_form(env, &mut local_ty);
            let mut inner_args = Vec::new();
            while let ExprContents::Pi(pi) = local_ty.contents {
                let inner_arg = pi.generate_local(meta_gen);
                inner_args.push(inner_arg.clone());
                local_ty = *pi.result;
                instantiate(
                    &mut local_ty,
                    &Expr::new_synthetic(ExprContents::LocalConstant(inner_arg)),
                );
                to_weak_head_normal_form(env, &mut local_ty);
            }

            get_indices(env, meta_gen, &local_ty, info).map(|intro_rule_indices| {
                // Create the application of the eliminator.
                let mut eliminator_application = info
                    .global_params
                    .iter()
                    .chain(std::iter::once(&rec_info.type_former))
                    .chain(&rec_info.minor_premises)
                    .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local.clone())))
                    .chain(intro_rule_indices.iter().copied().cloned())
                    .fold(eliminator.clone(), |func, arg| {
                        Expr::new_synthetic(ExprContents::Apply(Apply {
                            function: Box::new(func),
                            argument: Box::new(arg),
                        }))
                    });

                eliminator_application = Expr::new_synthetic(ExprContents::Apply(Apply {
                    function: Box::new(eliminator_application),
                    argument: Box::new(inner_args.iter().fold(
                        Expr::new_synthetic(ExprContents::LocalConstant(arg.clone())),
                        |func, arg| {
                            Expr::new_synthetic(ExprContents::Apply(Apply {
                                function: Box::new(func),
                                argument: Box::new(Expr::new_synthetic(
                                    ExprContents::LocalConstant(arg.clone()),
                                )),
                            }))
                        },
                    )),
                }));

                abstract_nary_lambda(
                    inner_args.into_iter(),
                    eliminator_application,
                    &Provenance::Synthetic,
                )
            })
        }))
        .bind(|eliminator_invocations| {
            let mut intro_rule_ty = intro_rule.ty.clone();
            while let ExprContents::Pi(pi) = intro_rule_ty.contents {
                let inner_arg = pi.generate_local(meta_gen);
                intro_rule_ty = *pi.result;
                instantiate(
                    &mut intro_rule_ty,
                    &Expr::new_synthetic(ExprContents::LocalConstant(inner_arg)),
                );
            }

            // Create the left hand side of the computation rule.
            let eliminator_arguments = info
                .global_params
                .iter()
                .chain(std::iter::once(&rec_info.type_former))
                .chain(&rec_info.minor_premises)
                .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local.clone())))
                .chain(
                    apply_args(&intro_rule_ty)
                        .into_iter()
                        .skip(info.global_params.len())
                        .cloned(),
                )
                .chain(std::iter::once(
                    info.global_params
                        .iter()
                        .chain(&split_result.nonrecursive_and_recursive)
                        .map(|local| {
                            Expr::new_synthetic(ExprContents::LocalConstant(local.clone()))
                        })
                        .fold(intro_rule_expr, |func, arg| {
                            Expr::new_synthetic(ExprContents::Apply(Apply {
                                function: Box::new(func),
                                argument: Box::new(arg),
                            }))
                        }),
                ));

            let eliminator_application = eliminator_arguments.fold(eliminator, |func, arg| {
                Expr::new_synthetic(ExprContents::Apply(Apply {
                    function: Box::new(func),
                    argument: Box::new(arg),
                }))
            });

            let computation_rule_lhs = abstract_nary_lambda(
                info.global_params
                    .iter()
                    .chain(std::iter::once(&rec_info.type_former))
                    .chain(&rec_info.minor_premises)
                    .chain(&split_result.nonrecursive_and_recursive)
                    .cloned(),
                eliminator_application.clone(),
                &Provenance::Synthetic,
            );

            // Create the right hand side of the computation rule.
            let minor_premise_application = split_result
                .nonrecursive_and_recursive
                .iter()
                .cloned()
                .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local)))
                .chain(eliminator_invocations)
                .fold(
                    Expr::new_synthetic(ExprContents::LocalConstant(minor_premise.clone())),
                    |func, arg| {
                        Expr::new_synthetic(ExprContents::Apply(Apply {
                            function: Box::new(func),
                            argument: Box::new(arg),
                        }))
                    },
                );

            let computation_rule_rhs = abstract_nary_lambda(
                info.global_params
                    .iter()
                    .chain(std::iter::once(&rec_info.type_former))
                    .chain(&rec_info.minor_premises)
                    .chain(&split_result.nonrecursive_and_recursive)
                    .cloned(),
                minor_premise_application.clone(),
                &Provenance::Synthetic,
            );

            typeck::infer_type(env, meta_gen, &computation_rule_lhs, true).bind(|ty_lhs| {
                // The type of the LHS of the computation rule was valid.
                typeck::infer_type(env, meta_gen, &computation_rule_rhs, true).bind(|ty_rhs| {
                    // The type of the RHS of the computation rule was valid.
                    // Check that the types are equal.
                    definitionally_equal(env, meta_gen, &ty_lhs, &ty_rhs).bind(|defeq| {
                        if defeq {
                            // The computation rule is valid.
                            Dr::ok(ComputationRule {
                                eliminator_application,
                                minor_premise_application,
                            })
                        } else {
                            Dr::fail(todo!())
                        }
                    })
                })
            })
        })
    })
}
