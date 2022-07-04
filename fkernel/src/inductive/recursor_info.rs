use fcommon::{Dr, Str, StrGenerator};
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::{
        Apply, BinderAnnotation, Expr, ExprContents, Inst, LocalConstant, MetavariableGenerator,
        Pi, Sort,
    },
    inductive::{Inductive, IntroRule},
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::{
        abstract_pi, apply_args, create_nary_application, create_nary_pi,
        destructure_as_nary_application, instantiate, ExprPrinter,
    },
    typeck::{as_sort, infer_type, to_weak_head_normal_form, Environment},
    universe::is_zero,
};

use super::{
    check::PartialInductiveInformation,
    check_intro_rule::{is_recursive_argument, is_valid_inductive_application},
};

pub fn recursor_info(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<RecursorInfo> {
    partial_recursor_info(env, meta_gen, ind, info).bind(|(major_premise, type_former)| {
        Dr::sequence(ind.contents.intro_rules.iter().map(|intro_rule| {
            minor_premise_info(env, meta_gen, ind, intro_rule, info, type_former.clone())
        }))
        .map(|minor_premises| {
            let mut is_k_target = is_zero(&info.sort.0) && ind.contents.intro_rules.len() == 1;
            let minor_premises = minor_premises
                .into_iter()
                .map(|(premise, is_k_target_inner)| {
                    is_k_target &= is_k_target_inner;
                    premise
                })
                .collect::<Vec<_>>();
            RecursorInfo {
                major_premise,
                type_former,
                minor_premises,
                is_k_target,
            }
        })
    })
}

/// Information about how the recursor will be constructed.
pub struct RecursorInfo {
    pub major_premise: LocalConstant,
    pub type_former: LocalConstant,
    pub minor_premises: Vec<LocalConstant>,
    pub is_k_target: bool,
}

/// Returns the major premise `n` and the type former `C`, stored as local constants.
fn partial_recursor_info(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<(LocalConstant, LocalConstant)> {
    let major_premise = LocalConstant {
        name: Name {
            provenance: Provenance::Synthetic,
            contents: env.db.intern_string_data("n".to_string()),
        },
        metavariable: meta_gen.gen(create_nary_application(
            Expr::new_synthetic(ExprContents::Inst(info.inst.clone())),
            info.global_params
                .iter()
                .chain(&info.index_params)
                .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local.clone()))),
            &Provenance::Synthetic,
        )),
        binder_annotation: BinderAnnotation::Explicit,
    };

    recursor_universe(env, meta_gen, ind, info).map(|recursor_universe| {
        // Construct the type of the type former C.
        let mut type_former_ty =
            Expr::new_synthetic(ExprContents::Sort(Sort(match recursor_universe {
                RecursorUniverse::Prop => Universe::new_synthetic(UniverseContents::UniverseZero),
                RecursorUniverse::Parameter(param) => Universe::new_synthetic(
                    UniverseContents::UniverseVariable(UniverseVariable(param)),
                ),
            })));
        // If we are performing dependent elimination, add the major premise as a parameter to the type former.
        if info.dependent_elimination {
            type_former_ty = Expr::new_synthetic(ExprContents::Pi(abstract_pi(
                major_premise.clone(),
                type_former_ty,
            )));
        }
        // Add the indices to the type former.
        type_former_ty = create_nary_pi(
            info.index_params.iter().cloned(),
            type_former_ty,
            &Provenance::Synthetic,
        );
        // Create the type former C.
        let type_former = LocalConstant {
            name: Name {
                provenance: Provenance::Synthetic,
                contents: env.db.intern_string_data("C".to_string()),
            },
            metavariable: meta_gen.gen(type_former_ty),
            binder_annotation: BinderAnnotation::Explicit,
        };

        (major_premise, type_former)
    })
}

/// Creates the minor premise associated to a given introduction rule.
/// Also returns `false` if this introduction rule forbids a K-style eliminator.
pub fn minor_premise_info(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    intro_rule: &IntroRule,
    info: &PartialInductiveInformation,
    type_former: LocalConstant,
) -> Dr<(LocalConstant, bool)> {
    split_intro_rule_type(env, meta_gen, ind, info, intro_rule.ty.clone()).bind(|split_result| {
        get_indices(env, meta_gen, &split_result.result_ty, info).bind(|indices| {
            let mut type_former_application = indices.iter().fold(
                Expr::new_synthetic(ExprContents::LocalConstant(type_former.clone())),
                |func, arg| {
                    Expr::new_synthetic(ExprContents::Apply(Apply {
                        function: Box::new(func),
                        argument: Box::new((*arg).clone()),
                    }))
                },
            );

            // If we're doing dependent elimination, provide the value being eliminated.
            if info.dependent_elimination {
                type_former_application = Expr::new_synthetic(ExprContents::Apply(Apply {
                    function: Box::new(type_former_application),
                    argument: Box::new(
                        info.global_params
                            .iter()
                            .chain(&split_result.nonrecursive_and_recursive)
                            .map(|local| {
                                Expr::new_synthetic(ExprContents::LocalConstant(local.clone()))
                            })
                            .fold(
                                Expr::new_synthetic(ExprContents::Inst(Inst {
                                    name: QualifiedName {
                                        provenance: Provenance::Synthetic,
                                        segments: info
                                            .inst
                                            .name
                                            .segments
                                            .iter()
                                            .rev()
                                            .skip(1)
                                            .rev()
                                            .chain(std::iter::once(&intro_rule.name))
                                            .cloned()
                                            .collect(),
                                    },
                                    universes: info.inst.universes.clone(),
                                })),
                                |func, arg| {
                                    Expr::new_synthetic(ExprContents::Apply(Apply {
                                        function: Box::new(func),
                                        argument: Box::new(arg),
                                    }))
                                },
                            ),
                    ),
                }));
            }

            // Create the set of inductive arguments from the set of recursive arguments.
            let mut str_gen = StrGenerator::new(
                env.db.up(),
                format!(
                    "ih_{}",
                    env.db.lookup_intern_string_data(intro_rule.name.contents)
                ),
            );
            let inductive_args =
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
                    }
                    get_indices(env, meta_gen, &local_ty, info).map(|intro_rule_indices| {
                        // Create the inner application of the minor premise.
                        let mut type_former_application = intro_rule_indices.iter().fold(
                            Expr::new_synthetic(ExprContents::LocalConstant(type_former.clone())),
                            |func, arg| {
                                Expr::new_synthetic(ExprContents::Apply(Apply {
                                    function: Box::new(func),
                                    argument: Box::new((*arg).clone()),
                                }))
                            },
                        );

                        // If we're doing dependent elimination, provide the value being eliminated.
                        if info.dependent_elimination {
                            type_former_application =
                                Expr::new_synthetic(ExprContents::Apply(Apply {
                                    function: Box::new(type_former_application),
                                    argument: inner_args.iter().fold(
                                        Box::new(Expr::new_synthetic(ExprContents::LocalConstant(
                                            arg.clone(),
                                        ))),
                                        |func, arg| {
                                            Box::new(Expr::new_synthetic(ExprContents::Apply(
                                                Apply {
                                                    function: func,
                                                    argument: Box::new(Expr::new_synthetic(
                                                        ExprContents::LocalConstant(arg.clone()),
                                                    )),
                                                },
                                            )))
                                        },
                                    ),
                                }));
                        }

                        // Create the new local constant.
                        LocalConstant {
                            name: Name {
                                provenance: Provenance::Synthetic,
                                contents: str_gen.generate(),
                            },
                            metavariable: meta_gen.gen(create_nary_pi(
                                inner_args.into_iter(),
                                type_former_application,
                                &Provenance::Synthetic,
                            )),
                            binder_annotation: BinderAnnotation::Explicit,
                        }
                    })
                }));

            inductive_args.map(|inductive_args| {
                let minor_premise_type = create_nary_pi(
                    split_result
                        .nonrecursive_and_recursive
                        .into_iter()
                        .chain(inductive_args),
                    type_former_application,
                    &Provenance::Synthetic,
                );
                (
                    LocalConstant {
                        name: Name {
                            provenance: Provenance::Synthetic,
                            contents: str_gen.generate(),
                        },
                        metavariable: meta_gen.gen(minor_premise_type),
                        binder_annotation: BinderAnnotation::Explicit,
                    },
                    split_result.is_k_target,
                )
            })
        })
    })
}

/// Splits the arguments to this intro rule into nonrecursive and recursive categories.
/// Returns the list of all parameters, then the list of recursive ones,
/// then the returned value after instantiating the intro rule with the parameters.
fn split_intro_rule_type(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
    mut e: Expr,
) -> Dr<SplitIntroRuleResult> {
    let mut nonrecursive_and_recursive = Vec::new();
    let mut recursive = Vec::new();
    let mut parameter_index = 0;
    let mut is_k_target = true;
    while let ExprContents::Pi(pi) = e.contents {
        if parameter_index < ind.contents.global_params {
            // This is a global parameter.
            e = *pi.result;
            instantiate(
                &mut e,
                &Expr::new_synthetic(ExprContents::LocalConstant(
                    info.global_params[parameter_index as usize].clone(),
                )),
            );
        } else {
            // This is an index parameter.
            is_k_target = false;
            let local = pi.generate_local(meta_gen);
            let is_recursive = is_recursive_argument(env, meta_gen, *pi.parameter_ty.clone(), info);
            if let Some(result) = is_recursive.value() {
                nonrecursive_and_recursive.push(local.clone());
                if *result {
                    recursive.push(local.clone());
                }
                e = *pi.result;
                instantiate(
                    &mut e,
                    &Expr::new_synthetic(ExprContents::LocalConstant(local)),
                );
            } else {
                return is_recursive.map(|_| todo!());
            }
        }
        parameter_index += 1;
    }
    Dr::ok(SplitIntroRuleResult {
        nonrecursive_and_recursive,
        recursive,
        result_ty: e,
        is_k_target,
    })
}

struct SplitIntroRuleResult {
    nonrecursive_and_recursive: Vec<LocalConstant>,
    recursive: Vec<LocalConstant>,
    result_ty: Expr,
    /// If this is true, this intro rule does not prevent a K-style eliminator.
    /// A declaration is a target for K-like reduction when it has one intro, the intro has zero
    /// (index) arguments, and it is a proposition.
    is_k_target: bool,
}

/// Given an expression of the form `(I As is)` where `I` is the inductive datatype being defined, `As` are the
/// global parameters, and `is` are the indices provided to it, return `is`.
fn get_indices<'a>(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    result_ty: &'a Expr,
    info: &PartialInductiveInformation,
) -> Dr<Vec<&'a Expr>> {
    is_valid_inductive_application(env, meta_gen, &result_ty, info).bind(|is_valid| {
        if is_valid {
            Dr::ok(
                apply_args(&result_ty)
                    .into_iter()
                    .skip(info.global_params.len())
                    .collect(),
            )
        } else {
            Dr::fail(todo!())
        }
    })
}

// TODO: document this
fn recursor_universe(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<RecursorUniverse> {
    eliminate_only_at_prop(env, meta_gen, ind, info).map(|result| {
        if result {
            // We must eliminate to `Prop`.
            RecursorUniverse::Prop
        } else {
            // We can eliminate to any universe.
            // Create a new universe parameter with a different name to all other universe parameters.
            RecursorUniverse::Parameter(
                (0..)
                    .find_map(|i| {
                        let param = env.db.intern_string_data(if i == 0 {
                            "l".to_string()
                        } else {
                            format!("l_{}", i)
                        });
                        if ind
                            .contents
                            .universe_params
                            .iter()
                            .all(|universe_param| universe_param.contents != param)
                        {
                            Some(param)
                        } else {
                            None
                        }
                    })
                    .unwrap(),
            )
        }
    })
}

enum RecursorUniverse {
    Prop,
    Parameter(Str),
}

/// Returns true if the type former C in the recursor can only map to `Prop`.
fn eliminate_only_at_prop(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<bool> {
    if info.never_zero {
        // The resultant inductive datatype is never in `Prop`, so the recursor may return any type.
        return Dr::ok(false);
    }

    if ind.contents.intro_rules.len() > 1 {
        // We have multiple introduction rules, so the type former can only map to `Prop`.
        return Dr::ok(true);
    }

    if ind.contents.intro_rules.is_empty() {
        // There are no introduction rules, so we can eliminate to anything.
        return Dr::ok(false);
    }

    // At this point, we know we have only one introduction rule.
    // We must perform one final check.
    // Each argument that is not a global parameter must either
    // - reside in `Prop`, or
    // - occur in the return type.
    // We can justify the second case by observing that the information that it is part of the type is not a secret.
    // By eliminating to a non-proposition, we would not be revealing anything that is not already known.
    let intro_rule = ind.contents.intro_rules.first().unwrap();
    let mut ty = intro_rule.ty.clone();
    let mut args_to_check = Vec::new();
    let mut parameter_index = 0;
    while let ExprContents::Pi(pi) = ty.contents {
        let local = pi.generate_local(meta_gen);
        if parameter_index >= ind.contents.global_params {
            let parameter_ty =
                infer_type(env, meta_gen, &pi.parameter_ty, true).bind(|ty| as_sort(env, ty));
            if let Some(result) = parameter_ty.value() {
                if !is_zero(&result.0) {
                    // The current argument is not in `Prop`.
                    // Check it later.
                    args_to_check.push(local.clone());
                }
            } else {
                return parameter_ty.map(|_| unreachable!());
            }
        }
        ty = *pi.result;
        instantiate(
            &mut ty,
            &Expr::new_synthetic(ExprContents::LocalConstant(local)),
        );
        parameter_index += 1;
    }

    // Every argument in `args_to_check` must occur in `ty_arguments`.
    let (ty_function, ty_arguments) = destructure_as_nary_application(&ty);
    for arg_to_check in args_to_check {
        if !ty_arguments.iter().any(|arg| {
            arg.eq_ignoring_provenance(&Expr::new_synthetic(ExprContents::LocalConstant(
                arg_to_check.clone(),
            )))
        }) {
            // The argument did not occur in `ty_arguments`.
            return Dr::ok(true);
        }
    }

    // All arguments are either in `Prop` or occur in `ty_arguments`.
    Dr::ok(false)
}