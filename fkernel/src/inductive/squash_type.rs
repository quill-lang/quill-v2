use fnodes::{
    basic_nodes::{Name, Provenance},
    expr::{
        Apply, BinderAnnotation, Delta, Expr, ExprContents, LocalConstant, MetavariableGenerator,
        Pi, Region,
    },
    inductive::{Inductive, InductiveContents, IntroRule},
};

use crate::{
    expr::abstract_pi,
    typeck::{to_weak_head_normal_form, Environment},
};

/// Generates the squashed version of an inductive type.
/// In particular, we create an almost identical copy of the inductive, where each argument to each intro rule
/// is converted into a delta-type, unless it already is, in which case, it is unchanged.
/// If there were no changes made to any intro rules, return [`None`] instead.
pub fn squashed_type(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
) -> Option<Inductive> {
    // Create the name of the squashed type.
    let squashed_name = Name {
        contents: env.db.intern_string_data(format!(
            "{}.squashed",
            env.db.lookup_intern_string_data(ind.contents.name.contents)
        )),
        provenance: ind.contents.name.provenance.clone(),
    };

    // Create the region parameter.
    let region = LocalConstant {
        name: Name {
            provenance: Provenance::Synthetic,
            contents: env.db.intern_string_data("r".to_string()),
        },
        metavariable: meta_gen.gen(Expr::new_synthetic(ExprContents::Region(Region))),
        binder_annotation: BinderAnnotation::Explicit,
    };

    let mut anything_modified = false;

    // Create the intro rules.
    let intro_rules = ind
        .contents
        .intro_rules
        .iter()
        .map(|intro_rule| {
            let (ty, modified) = wrap_args_with_delta(
                env,
                &region,
                &squashed_name,
                ind.contents.global_params,
                &intro_rule.ty,
            );
            anything_modified |= modified;
            IntroRule {
                name: Name {
                    contents: env.db.intern_string_data(format!(
                        "{}.squashed",
                        env.db.lookup_intern_string_data(intro_rule.name.contents)
                    )),
                    provenance: intro_rule.name.provenance.clone(),
                },
                ty: Expr::new_synthetic(ExprContents::Pi(abstract_pi(region.clone(), ty))),
            }
        })
        .collect::<Vec<_>>();

    if anything_modified {
        Some(Inductive {
            provenance: ind.provenance.clone(),
            contents: InductiveContents {
                name: squashed_name,
                universe_params: ind.contents.universe_params.clone(),
                ty: Expr::new_synthetic(ExprContents::Pi(abstract_pi(
                    region,
                    ind.contents.ty.clone(),
                ))),
                global_params: ind.contents.global_params + 1,
                intro_rules,
            },
        })
    } else {
        None
    }
}

/// If this expression is a [`Pi`], all of its arguments are wrapped using `wrap_delta`, then it is returned.
/// Returns false if no modifications were done to `e`.
/// The value in `ignore_args` is the amount of arguments to *ignore* wrapping.
/// This is initially set to the number of global parameters.
///
/// TODO: What happens with index parameters?
fn wrap_args_with_delta(
    env: &Environment,
    region: &LocalConstant,
    squashed_name: &Name,
    ignore_args: u32,
    e: &Expr,
) -> (Expr, bool) {
    match &e.contents {
        ExprContents::Pi(pi) => {
            let (parameter_ty, parameter_modified) = if ignore_args == 0 {
                let (parameter_ty, parameter_modified) =
                    wrap_delta(env, region, *pi.parameter_ty.clone());
                (
                    Expr::new_with_provenance(
                        &pi.parameter_ty.provenance,
                        ExprContents::Delta(parameter_ty),
                    ),
                    parameter_modified,
                )
            } else {
                (*pi.parameter_ty.clone(), false)
            };

            let (result, result_modified) = wrap_args_with_delta(
                env,
                region,
                squashed_name,
                ignore_args.saturating_sub(1),
                &pi.result,
            );
            (
                Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Pi(Pi {
                        parameter_name: pi.parameter_name.clone(),
                        binder_annotation: pi.binder_annotation,
                        parameter_ty: Box::new(parameter_ty),
                        result: Box::new(result),
                    }),
                ),
                parameter_modified || result_modified,
            )
        }
        _ => {
            // This should be an invocation of the inductive data type.
            // We need to change the name to the name of the squashed type, and also add the region parameter.
            let mut result = e.clone();
            let mut name = &mut result;
            loop {
                match &mut name.contents {
                    ExprContents::Apply(apply) => {
                        name = &mut apply.function;
                    }
                    contents => {
                        let mut name_taken =
                            std::mem::replace(contents, ExprContents::Region(Region));
                        if let ExprContents::Inst(inst) = &mut name_taken {
                            *inst.name.segments.last_mut().unwrap() = squashed_name.clone();
                        } else {
                            unreachable!()
                        }
                        *contents = ExprContents::Apply(Apply {
                            function: Box::new(Expr::new_synthetic(name_taken)),
                            argument: Box::new(Expr::new_synthetic(ExprContents::LocalConstant(
                                region.clone(),
                            ))),
                        });
                        break;
                    }
                }
            }

            (result, false)
        }
    }
}

/// If this was not a delta type, wrap it in a [`Delta`].
/// The given local constant is the region.
/// If this function also returns false, no modifications were done to `e`, and it is being
/// returned verbatim.
fn wrap_delta(env: &Environment, region: &LocalConstant, e: Expr) -> (Delta, bool) {
    match as_delta(env, e.clone()) {
        Some(delta) => {
            // This was already a delta type.
            // Hence, we can return it verbatim, with the same region.
            (delta, false)
        }
        None => {
            // This was not a delta type.
            // Encase it in a delta.
            (
                Delta {
                    region: Box::new(Expr::new_synthetic(ExprContents::LocalConstant(
                        region.clone(),
                    ))),
                    ty: Box::new(e),
                },
                true,
            )
        }
    }
}

/// Expands the given expression until it is a [`Delta`].
/// If the expression was not a delta, returns [`None`].
pub fn as_delta(env: &Environment, mut e: Expr) -> Option<Delta> {
    if let ExprContents::Delta(delta) = e.contents {
        Some(delta)
    } else {
        to_weak_head_normal_form(env, &mut e);
        if let ExprContents::Delta(delta) = e.contents {
            Some(delta)
        } else {
            None
        }
    }
}
