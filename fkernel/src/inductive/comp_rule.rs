use std::collections::HashMap;

use fcommon::Dr;
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::*,
    inductive::{Inductive, IntroRule},
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::{
        abstract_nary_lambda, apply_args, instantiate, replace_local, replace_universe_variable,
        ExprPrinter,
    },
    typeck::{self, definitionally_equal, to_weak_head_normal_form, Environment},
    universe::instantiate_universe_variable,
};

use super::{
    check::PartialInductiveInformation,
    recursor_info::{get_indices, split_intro_rule_type, RecursorInfo, RecursorUniverse},
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
                .map_reports(|report| {
                    report.with_note(format!(
                        "error raised while creating the computation rule for intro rule {} on type {}",
                        env.db.lookup_intern_string_data(intro_rule.name.contents),
                        env.db.lookup_intern_string_data(ind.contents.name.contents)
                    ))
                })
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
///
/// Suppose that we have an eliminator application of the form `I.rec p (I.intro_i q)` where `p` is a list of parameters to the eliminator,
/// and `(I.intro_i q)` is the major premise, formed of an intro rule `I.intro_i` and a list of parameters `q`.
/// The computation rule for this intro rule is a rewrite rule for converting expressions of this form into their evaluated forms,
/// where the recursor is not at the head of the expression.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ComputationRule {
    eliminator_application: Expr,
    minor_premise_application: Expr,
}

impl ComputationRule {
    /// See [`ComputationRule`] for more information.
    ///
    /// To evaluate an expression of the form `I.rec p (I.intro_i q)` using a computation rule, we return a copy of `minor_premise_application`,
    /// where the local constants in `parameters` and `intro_rule_args` have been replaced with the corresponding values in `p` and `q`.
    ///
    /// Returns [`None`] if this was not a valid instance of the computation rule.
    pub fn evaluate(&self, eliminator_application: &Expr) -> Option<Expr> {
        pattern_match(self.eliminator_application.clone(), eliminator_application).map(|result| {
            let mut application = self.minor_premise_application.clone();
            result.replace(&mut application);
            application
        })
    }

    pub fn eliminator_application(&self) -> &Expr {
        &self.eliminator_application
    }
}

#[derive(Default)]
struct PatternMatchResult<'a> {
    local_map: HashMap<LocalConstant, &'a Expr>,
    universe_map: HashMap<UniverseVariable, &'a Universe>,
}

impl<'a> PatternMatchResult<'a> {
    pub fn replace(&self, e: &mut Expr) {
        for (local, replacement) in self.local_map.iter() {
            replace_local(e, local, replacement);
        }
        for (var, replacement) in self.universe_map.iter() {
            replace_universe_variable(e, var, replacement);
        }
    }

    fn replace_universe(&self, u: &mut Universe) {
        for (var, replacement) in self.universe_map.iter() {
            instantiate_universe_variable(u, var, replacement);
        }
    }

    /// Combines two pattern match results into a single result.
    pub fn with(mut self, other: Self) -> Self {
        self.local_map.extend(other.local_map);
        self.universe_map.extend(other.universe_map);
        self
    }
}

/// Takes a pattern expression containing local constants together with a target expression which we suppose matches the pattern.
/// The target expression should not contain local constants or metavariables, and the pattern should not contain metavariables.
/// This function will try to replace the local constants in the pattern with expressions sourced from the target expression such that the resulting
/// pattern expression after the substitution is equal to the target expression. If no substitution could be found, return `None`.
fn pattern_match(pattern: Expr, target: &Expr) -> Option<PatternMatchResult> {
    match (pattern.contents, &target.contents) {
        (ExprContents::Bound(pattern_bound), ExprContents::Bound(target_bound)) => {
            if pattern_bound.index == target_bound.index {
                Some(PatternMatchResult::default())
            } else {
                None
            }
        }
        (ExprContents::Inst(pattern_inst), ExprContents::Inst(target_inst)) => {
            if pattern_inst.name.eq_ignoring_provenance(&target_inst.name) {
                pattern_inst
                    .universes
                    .into_iter()
                    .zip(&target_inst.universes)
                    .fold(
                        Some(PatternMatchResult::default()),
                        |map, (pattern, target)| {
                            map.and_then(|map| {
                                pattern_match_universe(pattern, target)
                                    .map(|inner_map| map.with(inner_map))
                            })
                        },
                    )
            } else {
                None
            }
        }
        (ExprContents::Let(mut pattern_let), ExprContents::Let(target_let)) => {
            pattern_match(*pattern_let.to_assign, &target_let.to_assign).and_then(|map| {
                map.replace(&mut pattern_let.body);
                pattern_match(*pattern_let.body, &target_let.to_assign)
                    .map(|inner_map| map.with(inner_map))
            })
        }
        (ExprContents::Lambda(mut pattern_lambda), ExprContents::Lambda(target_lambda)) => {
            pattern_match(*pattern_lambda.parameter_ty, &target_lambda.parameter_ty).and_then(
                |map| {
                    map.replace(&mut pattern_lambda.result);
                    pattern_match(*pattern_lambda.result, &target_lambda.result)
                        .map(|inner_map| map.with(inner_map))
                },
            )
        }
        (ExprContents::Pi(mut pattern_pi), ExprContents::Pi(target_pi)) => {
            pattern_match(*pattern_pi.parameter_ty, &target_pi.parameter_ty).and_then(|map| {
                map.replace(&mut pattern_pi.result);
                pattern_match(*pattern_pi.result, &target_pi.result)
                    .map(|inner_map| map.with(inner_map))
            })
        }
        (ExprContents::Apply(mut pattern_apply), ExprContents::Apply(target_apply)) => {
            pattern_match(*pattern_apply.function, &target_apply.function).and_then(|map| {
                map.replace(&mut pattern_apply.argument);
                pattern_match(*pattern_apply.argument, &target_apply.argument)
                    .map(|inner_map| map.with(inner_map))
            })
        }
        (ExprContents::Sort(pattern_sort), ExprContents::Sort(target_sort)) => {
            pattern_match_universe(pattern_sort.0, &target_sort.0)
        }
        (ExprContents::LocalConstant(pattern_local), _) => {
            // Replace the given local constant with the replacement.
            let mut map = PatternMatchResult::default();
            map.local_map.insert(pattern_local, target);
            Some(map)
        }
        _ => None,
    }
}

/// Performs the same task as [`pattern_match`], but operates on universes instead of expressions.
fn pattern_match_universe(pattern: Universe, target: &Universe) -> Option<PatternMatchResult> {
    match (pattern.contents, &target.contents) {
        (UniverseContents::UniverseZero, UniverseContents::UniverseZero) => {
            Some(PatternMatchResult::default())
        }
        (
            UniverseContents::UniverseSucc(pattern_inner),
            UniverseContents::UniverseSucc(target_inner),
        ) => pattern_match_universe(*pattern_inner.0, &target_inner.0),
        (
            UniverseContents::UniverseMax(mut pattern_max),
            UniverseContents::UniverseMax(target_max),
        ) => pattern_match_universe(*pattern_max.left, &target_max.left).and_then(|map| {
            map.replace_universe(&mut pattern_max.right);
            pattern_match_universe(*pattern_max.right, &target_max.right)
                .map(|inner_map| map.with(inner_map))
        }),
        (
            UniverseContents::UniverseImpredicativeMax(mut pattern_imax),
            UniverseContents::UniverseImpredicativeMax(target_imax),
        ) => pattern_match_universe(*pattern_imax.left, &target_imax.left).and_then(|map| {
            map.replace_universe(&mut pattern_imax.right);
            pattern_match_universe(*pattern_imax.right, &target_imax.right)
                .map(|inner_map| map.with(inner_map))
        }),
        (UniverseContents::UniverseVariable(pattern_var), _) => {
            // Replace the given universe variable with the replacement.
            let mut map = PatternMatchResult::default();
            map.universe_map.insert(pattern_var, target);
            Some(map)
        }
        _ => None,
    }
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

    let eliminator_universe = match rec_info.recursor_universe {
        RecursorUniverse::Prop => Vec::new(),
        RecursorUniverse::Parameter(param) => vec![Name {
            provenance: ind.provenance.clone(),
            contents: param,
        }],
    };

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
        universes: eliminator_universe
            .iter()
            .chain(&ind.contents.universe_params)
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
