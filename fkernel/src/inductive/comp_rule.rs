use fcommon::Dr;
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::*,
    inductive::{Inductive, IntroRule},
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::{
        abstract_lambda, abstract_nary_lambda, create_nary_application, instantiate, ExprPrinter,
    },
    typeck::{self, to_weak_head_normal_form, Environment},
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
) -> Dr<Vec<Expr>> {
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
            tracing::info!("computation rule has value {}", print.print(rule));
        }
        rules
    })
}

fn generate_computation_rule(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    intro_rule: &IntroRule,
    minor_premise: &LocalConstant,
    info: &PartialInductiveInformation,
    rec_info: &RecursorInfo,
) -> Dr<Expr> {
    split_intro_rule_type(env, meta_gen, ind, info, intro_rule.ty.clone()).bind(|split_result| {
        Dr::sequence(split_result.recursive.iter().enumerate().map(|(i, arg)| {
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

                let mut eliminator_application = info
                    .global_params
                    .iter()
                    .chain(std::iter::once(&rec_info.type_former))
                    .chain(&rec_info.minor_premises)
                    .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local.clone())))
                    .chain(intro_rule_indices.iter().copied().cloned())
                    .fold(eliminator, |func, arg| {
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

            // Create the right hand side of the computation rule.
            let computation_rule_rhs = abstract_nary_lambda(
                info.global_params
                    .iter()
                    .chain(std::iter::once(&rec_info.type_former))
                    .chain(&rec_info.minor_premises)
                    .chain(&split_result.nonrecursive_and_recursive)
                    .cloned(),
                minor_premise_application,
                &Provenance::Synthetic,
            );

            typeck::infer_type(env, meta_gen, &computation_rule_rhs, true).map(|_| {
                // The type of the RHS of the computation rule was valid.
                computation_rule_rhs
            })
        })
    })
}
