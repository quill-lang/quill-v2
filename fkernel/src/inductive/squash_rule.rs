use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::{
        Apply, BinderAnnotation, Borrow, Expr, ExprContents, Inst, LocalConstant,
        MetavariableGenerator, Region,
    },
    inductive::Inductive,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::typeck::Environment;

use super::{comp_rule::ComputationRule, squash_type::as_delta};

/// Creates the computation rules for computing outputs of the squash function.
pub fn generate_squash_rules(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    squashed: &Inductive,
) -> Vec<ComputationRule> {
    ind.contents
        .intro_rules
        .iter()
        .zip(&squashed.contents.intro_rules)
        .map(|(intro_rule, squashed_intro_rule)| {
            // Compute the squash rule for this intro rule pair.
            let args = pi_args(&intro_rule.ty, meta_gen);
            let squash_args = pi_args(&squashed_intro_rule.ty, meta_gen);
            let region = squash_args.get(0).cloned().unwrap_or_else(|| {
                // If there was no region parameter (e.g. if there are no fields that need to be squashed), we need to make our own region parameter.
                LocalConstant {
                    name: Name {
                        provenance: Provenance::Synthetic,
                        contents: env.db.intern_string_data("r".to_string()),
                    },
                    metavariable: meta_gen.gen(Expr::new_synthetic(ExprContents::Region(Region))),
                    binder_annotation: BinderAnnotation::Explicit,
                }
            });
            let intro_rule_name = QualifiedName {
                provenance: Provenance::Synthetic,
                segments: env
                    .db
                    .lookup_intern_path_data(env.source.path)
                    .0
                    .into_iter()
                    .chain(std::iter::once(intro_rule.name.contents))
                    .map(|s| Name {
                        provenance: Provenance::Synthetic,
                        contents: s,
                    })
                    .collect(),
            };
            let squashed_intro_rule_name = QualifiedName {
                provenance: Provenance::Synthetic,
                segments: env
                    .db
                    .lookup_intern_path_data(env.source.path)
                    .0
                    .into_iter()
                    .chain(std::iter::once(squashed_intro_rule.name.contents))
                    .map(|s| Name {
                        provenance: Provenance::Synthetic,
                        contents: s,
                    })
                    .collect(),
            };

            let pattern = Expr::new_synthetic(ExprContents::Borrow(Borrow {
                region: Box::new(Expr::new_synthetic(ExprContents::LocalConstant(
                    region.clone(),
                ))),
                value: Box::new(
                    args.iter().fold(
                        Expr::new_synthetic(ExprContents::Inst(Inst {
                            name: intro_rule_name,
                            universes: ind
                                .contents
                                .universe_params
                                .iter()
                                .map(|name| {
                                    Universe::new_synthetic(UniverseContents::UniverseVariable(
                                        UniverseVariable(name.contents),
                                    ))
                                })
                                .collect(),
                        })),
                        |func, arg| {
                            Expr::new_synthetic(ExprContents::Apply(Apply {
                                function: Box::new(func),
                                argument: Box::new(Expr::new_synthetic(
                                    ExprContents::LocalConstant(arg.clone()),
                                )),
                            }))
                        },
                    ),
                ),
            }));

            let args = if args.len() == squash_args.len() {
                Box::new(args.into_iter()) as Box<dyn Iterator<Item = _>>
            } else {
                assert_eq!(args.len() + 1, squash_args.len());
                Box::new(std::iter::once(region.clone()).chain(args))
            };

            let replacement = args.zip(squash_args).enumerate().fold(
                Expr::new_synthetic(ExprContents::Inst(Inst {
                    name: squashed_intro_rule_name,
                    universes: ind
                        .contents
                        .universe_params
                        .iter()
                        .map(|name| {
                            Universe::new_synthetic(UniverseContents::UniverseVariable(
                                UniverseVariable(name.contents),
                            ))
                        })
                        .collect(),
                })),
                |func, (i, (arg, squash_arg))| {
                    Expr::new_synthetic(ExprContents::Apply(Apply {
                        function: Box::new(func),
                        argument: Box::new({
                            if i >= squashed.contents.global_params as usize {
                                match as_delta(env, *arg.metavariable.ty).is_some() {
                                    true => {
                                        // This is already a borrowed type, so we don't need to borrow it again.
                                        Expr::new_synthetic(ExprContents::LocalConstant(squash_arg))
                                    }
                                    false => {
                                        // This is not a borrowed type. We need to insert a borrow manually.
                                        Expr::new_synthetic(ExprContents::Borrow(Borrow {
                                            region: Box::new(Expr::new_synthetic(
                                                ExprContents::LocalConstant(region.clone()),
                                            )),
                                            value: Box::new(Expr::new_synthetic(
                                                ExprContents::LocalConstant(squash_arg),
                                            )),
                                        }))
                                    }
                                }
                            } else {
                                // This is a global parameter, so leave it unchanged.
                                Expr::new_synthetic(ExprContents::LocalConstant(squash_arg))
                            }
                        }),
                    }))
                },
            );
            ComputationRule::new(pattern, replacement)
        })
        .collect()
}

/// Returns the arguments, in order, to a [`Pi`].
/// Discards the return value.
fn pi_args(mut e: &Expr, meta_gen: &mut MetavariableGenerator) -> Vec<LocalConstant> {
    let mut result = Vec::new();
    while let ExprContents::Pi(pi) = &e.contents {
        e = &pi.result;
        result.push(pi.generate_local(meta_gen));
    }
    result
}
