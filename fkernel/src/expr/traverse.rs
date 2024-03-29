//! Utilities for traversing the expression tree for things like find-and-replace operations.

use std::cell::Cell;

use fcommon::Str;
use fnodes::{
    basic_nodes::{DeBruijnIndex, DeBruijnOffset, Name},
    expr::*,
    universe::{Universe, UniverseVariable},
};

use crate::{
    typeck::{definition_height, DefinitionHeight, Environment},
    universe::{instantiate_universe, instantiate_universe_variable},
};

enum ReplaceResult {
    /// The expression should not be replaced.
    Skip,
    /// The expression should be replaced with the given value.
    ReplaceWith(Expr),
}

/// Traverses the expression tree and finds expressions matching the provided replacement function.
/// If any matched, the replacement function generates the value to replace the found value with.
/// The provided [`DeBruijnOffset`] gives the amount of binders the [`Expr`] argument is currently under.
fn replace_in_expr(
    e: &mut Expr,
    replace_fn: impl Clone + Fn(&Expr, DeBruijnOffset) -> ReplaceResult,
) {
    replace_in_expr_offset(e, replace_fn, DeBruijnOffset::zero())
}

/// Like [`replace_in_expr`] but keeps track of sub-expression de Bruijn index offsets.
fn replace_in_expr_offset(
    e: &mut Expr,
    replace_fn: impl Clone + Fn(&Expr, DeBruijnOffset) -> ReplaceResult,
    offset: DeBruijnOffset,
) {
    // Invoke the replacement function.
    match replace_fn(e, offset) {
        ReplaceResult::Skip => {
            // Traverse the sub-expressions of `e`.
            match &mut e.contents {
                ExprContents::Borrow(borrow) => {
                    replace_in_expr_offset(&mut borrow.region, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut borrow.value, replace_fn, offset);
                }
                ExprContents::LocalConstant(local) => {
                    replace_in_expr_offset(&mut local.metavariable.ty, replace_fn, offset);
                }
                ExprContents::Metavariable(var) => {
                    replace_in_expr_offset(&mut var.ty, replace_fn, offset);
                }
                ExprContents::Let(let_expr) => {
                    replace_in_expr_offset(&mut let_expr.to_assign, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut let_expr.to_assign_ty, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut let_expr.body, replace_fn, offset.succ());
                }
                ExprContents::Lambda(lambda) => {
                    replace_in_expr_offset(&mut lambda.parameter_ty, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut lambda.result, replace_fn, offset.succ());
                }
                ExprContents::Pi(pi) => {
                    replace_in_expr_offset(&mut pi.parameter_ty, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut pi.result, replace_fn, offset.succ());
                }
                ExprContents::Delta(delta) => {
                    replace_in_expr_offset(&mut delta.region, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut delta.ty, replace_fn, offset);
                }
                ExprContents::Apply(apply) => {
                    replace_in_expr_offset(&mut apply.function, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut apply.argument, replace_fn, offset);
                }
                _ => {}
            }
        }
        ReplaceResult::ReplaceWith(e_replaced) => {
            // We replace `e` with the given value.
            // We don't try to traverse the sub-expressions of this returned value.
            *e = e_replaced;
        }
    }
}

/// Traverses the expression tree and finds expressions matching the provided predicate.
/// If any return `true`, the first such expression is returned.
/// The tree is traversed depth first.
fn find_in_expr(
    e: &Expr,
    predicate: impl Clone + Fn(&Expr, DeBruijnOffset) -> bool,
) -> Option<&Expr> {
    find_in_expr_offset(e, predicate, DeBruijnOffset::zero())
}

/// Like [`find_in_expr`] but keeps track of sub-expression de Bruijn index offsets.
fn find_in_expr_offset(
    e: &Expr,
    predicate: impl Clone + Fn(&Expr, DeBruijnOffset) -> bool,
    offset: DeBruijnOffset,
) -> Option<&Expr> {
    if predicate(e, offset) {
        Some(e)
    } else {
        match &e.contents {
            ExprContents::Borrow(borrow) => {
                find_in_expr_offset(&borrow.region, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&borrow.value, predicate, offset))
            }
            ExprContents::LocalConstant(local) => {
                find_in_expr_offset(&local.metavariable.ty, predicate, offset)
            }
            ExprContents::Metavariable(var) => find_in_expr_offset(&var.ty, predicate, offset),
            ExprContents::Let(let_expr) => {
                find_in_expr_offset(&let_expr.to_assign, predicate.clone(), offset).or_else(|| {
                    find_in_expr_offset(&let_expr.to_assign_ty, predicate.clone(), offset)
                        .or_else(|| find_in_expr_offset(&let_expr.body, predicate, offset.succ()))
                })
            }
            ExprContents::Lambda(lambda) => {
                find_in_expr_offset(&lambda.parameter_ty, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&lambda.result, predicate, offset.succ()))
            }
            ExprContents::Pi(pi) => {
                find_in_expr_offset(&pi.parameter_ty, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&pi.result, predicate, offset.succ()))
            }
            ExprContents::Delta(delta) => {
                find_in_expr_offset(&delta.region, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&delta.ty, predicate, offset))
            }
            ExprContents::Apply(apply) => {
                find_in_expr_offset(&apply.function, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&apply.argument, predicate, offset))
            }
            _ => None,
        }
    }
}

/// Returns the first local constant or metavariable in the given expression.
pub fn first_local_or_metavariable(e: &Expr) -> Option<&Expr> {
    find_in_expr(e, |inner, _offset| {
        matches!(
            &inner.contents,
            ExprContents::LocalConstant(_) | ExprContents::Metavariable(_)
        )
    })
}

/// Gets the maximum height of reducible definitions contained inside this expression.
pub fn get_max_height(env: &Environment, e: &Expr) -> DefinitionHeight {
    let height = Cell::new(0);
    find_in_expr(e, |inner, _offset| {
        if let ExprContents::Inst(inst) = &inner.contents {
            if let Some(inner_height) = definition_height(env, inst) {
                height.replace(std::cmp::max(height.get(), inner_height));
            }
        }
        false
    });
    height.into_inner()
}

/// Finds the first instance of the given constant in the expression.
/// The constant is given as a list of name segments, so that this function doesn't depend on the database.
pub fn find_constant<'e>(e: &'e Expr, segments: &[Str]) -> Option<&'e Inst> {
    find_in_expr(e, |inner, _offset| {
        if let ExprContents::Inst(inst) = &inner.contents {
            inst.name
                .segments
                .iter()
                .map(|name| name.contents)
                .collect::<Vec<_>>()
                == segments
        } else {
            false
        }
    })
    .map(|expr| {
        if let ExprContents::Inst(inst) = &expr.contents {
            inst
        } else {
            unreachable!()
        }
    })
}

/// Instantiate the first bound variable with the given substitution.
/// This will subtract one from all higher de Bruijn indices.
pub fn instantiate(e: &mut Expr, substitution: &Expr) {
    replace_in_expr(e, |e, offset| {
        match &e.contents {
            ExprContents::Bound(Bound { index }) => {
                match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                    std::cmp::Ordering::Less => {
                        // The variable is bound and has index lower than the offset, so we don't change it.
                        ReplaceResult::Skip
                    }
                    std::cmp::Ordering::Equal => {
                        // The variable is the smallest free de Bruijn index.
                        // It is exactly the one we need to substitute.
                        let mut substitution = substitution.clone();
                        lift_free_vars(&mut substitution, offset);
                        ReplaceResult::ReplaceWith(substitution)
                    }
                    std::cmp::Ordering::Greater => {
                        // This de Bruijn index must be decremented, since we just
                        // instantiated a variable below it.
                        let mut e = e.clone();
                        if let ExprContents::Bound(Bound { index }) = &mut e.contents {
                            *index = index.pred();
                        } else {
                            unreachable!()
                        }
                        ReplaceResult::ReplaceWith(e)
                    }
                }
            }
            _ => ReplaceResult::Skip,
        }
    })
}

/// Replace the given list of universe parameters with the given arguments.
/// The lists must be the same length.
pub fn instantiate_universe_parameters(
    e: &mut Expr,
    universe_params: &[Name],
    universe_arguments: &[Universe],
) {
    replace_in_expr(e, |e, _offset| match &e.contents {
        ExprContents::Inst(inst) => {
            let mut replace = inst.clone();
            for univ in &mut replace.universes {
                for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                    instantiate_universe(univ, UniverseVariable(param.contents), replacement);
                }
            }
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::Inst(replace),
            ))
        }
        ExprContents::Sort(sort) => {
            let mut replace = sort.clone();
            for (param, replacement) in universe_params.iter().zip(universe_arguments) {
                instantiate_universe(
                    &mut replace.0,
                    UniverseVariable(param.contents),
                    replacement,
                );
            }
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::Sort(replace),
            ))
        }
        _ => ReplaceResult::Skip,
    })
}

/// Increase the de Bruijn indices of free variables by a certain offset.
pub fn lift_free_vars(e: &mut Expr, shift: DeBruijnOffset) {
    replace_in_expr(e, |e, offset| {
        match &e.contents {
            ExprContents::Bound(Bound { index }) => {
                if *index >= DeBruijnIndex::zero() + offset {
                    // The variable is free.
                    let mut e = e.clone();
                    if let ExprContents::Bound(Bound { index }) = &mut e.contents {
                        *index = *index + shift;
                    } else {
                        unreachable!()
                    }
                    ReplaceResult::ReplaceWith(e)
                } else {
                    ReplaceResult::Skip
                }
            }
            _ => ReplaceResult::Skip,
        }
    })
}

/// Create a lambda expression where the parameter is the given local constant.
pub fn abstract_lambda(local: LocalConstant, mut return_type: Expr) -> Lambda {
    replace_in_expr(&mut return_type, |e, offset| match &e.contents {
        ExprContents::LocalConstant(inner_local) => {
            if *inner_local == local {
                ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Bound(Bound {
                        index: DeBruijnIndex::zero() + offset,
                    }),
                ))
            } else {
                ReplaceResult::Skip
            }
        }
        _ => ReplaceResult::Skip,
    });
    Lambda {
        parameter_name: local.name,
        binder_annotation: local.binder_annotation,
        parameter_ty: local.metavariable.ty,
        result: Box::new(return_type),
    }
}

/// Create a pi expression where the parameter is the given local constant.
pub fn abstract_pi(local: LocalConstant, mut return_type: Expr) -> Pi {
    replace_in_expr(&mut return_type, |e, offset| match &e.contents {
        ExprContents::LocalConstant(inner_local) => {
            if *inner_local == local {
                ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Bound(Bound {
                        index: DeBruijnIndex::zero() + offset,
                    }),
                ))
            } else {
                ReplaceResult::Skip
            }
        }
        _ => ReplaceResult::Skip,
    });
    Pi {
        parameter_name: local.name,
        binder_annotation: local.binder_annotation,
        parameter_ty: local.metavariable.ty,
        result: Box::new(return_type),
    }
}

/// Replace the given local constant with this expression.
pub fn replace_local(e: &mut Expr, local: &LocalConstant, replacement: &Expr) {
    replace_in_expr(e, |e, offset| {
        if let ExprContents::LocalConstant(inner) = &e.contents
            && inner.metavariable.index == local.metavariable.index {
            // We should replace this local variable.
            let mut replacement = replacement.clone();
            lift_free_vars(&mut replacement, offset);
            ReplaceResult::ReplaceWith(replacement)
        } else {
            ReplaceResult::Skip
        }
    })
}

pub fn replace_universe_variable(e: &mut Expr, var: &UniverseVariable, replacement: &Universe) {
    replace_in_expr(e, |e, _offset| match &e.contents {
        ExprContents::Inst(inst) => {
            let mut inst = inst.clone();
            for u in &mut inst.universes {
                instantiate_universe_variable(u, var, replacement);
            }
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::Inst(inst),
            ))
        }
        ExprContents::Sort(sort) => {
            let mut u = sort.0.clone();
            instantiate_universe_variable(&mut u, var, replacement);
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::Sort(Sort(u)),
            ))
        }
        ExprContents::Metavariable(meta) => {
            let mut ty = meta.ty.clone();
            replace_universe_variable(&mut ty, var, replacement);
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::Metavariable(Metavariable { ty, ..meta.clone() }),
            ))
        }
        ExprContents::LocalConstant(local) => {
            let mut ty = local.metavariable.ty.clone();
            replace_universe_variable(&mut ty, var, replacement);
            ReplaceResult::ReplaceWith(Expr::new_with_provenance(
                &e.provenance,
                ExprContents::LocalConstant(LocalConstant {
                    metavariable: Metavariable {
                        ty,
                        ..local.metavariable
                    },
                    ..local.clone()
                }),
            ))
        }
        _ => ReplaceResult::Skip,
    })
}
