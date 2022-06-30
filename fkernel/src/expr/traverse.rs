//! Utilities for traversing the expression tree for things like find-and-replace operations.

use fnodes::{
    basic_nodes::{DeBruijnIndex, DeBruijnOffset, Name},
    expr::*,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::universe::instantiate_universe;

enum ReplaceResult {
    /// The expression should not be replaced.
    Skip,
    /// The expression should be replaced with the given value.
    ReplaceWith(Expr),
}

/// Traverses the expression tree and finds expressions matching the provided replacement function.
/// If any matched, the replacement function generates the value to replace the found value with.
/// The provided [`DeBruijnOffset`] gives the amount of binders the [`Expr`] argument is currently under.
///
/// Replacement occurs in types of expressions as well as their values.
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
                ExprContents::Let(let_expr) => {
                    replace_in_expr_offset(&mut let_expr.to_assign, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut let_expr.body, replace_fn.clone(), offset.succ());
                }
                ExprContents::Lambda(lambda) => {
                    replace_in_expr_offset(&mut lambda.parameter_ty, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut lambda.result, replace_fn.clone(), offset.succ());
                }
                ExprContents::Pi(pi) => {
                    replace_in_expr_offset(&mut pi.parameter_ty, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut pi.result, replace_fn.clone(), offset.succ());
                }
                ExprContents::Apply(apply) => {
                    replace_in_expr_offset(&mut apply.function, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut apply.argument, replace_fn.clone(), offset);
                }
                _ => {}
            }
            // Replace any instances of the pattern in the type of the expression as well.
            if let Some(ty) = &mut e.ty {
                replace_in_expr_offset(ty, replace_fn, offset);
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
///
/// The find operation occurs in types of expressions as well as their values.
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
            ExprContents::Let(let_expr) => {
                find_in_expr_offset(
                    &let_expr.to_assign,
                    // To avoid requiring `Clone` on `replace_fn`, we can just make an inner function that calls `replace_fun`.
                    predicate.clone(),
                    offset,
                )
                .or_else(|| find_in_expr_offset(&let_expr.body, predicate.clone(), offset.succ()))
            }
            ExprContents::Lambda(lambda) => {
                find_in_expr_offset(&lambda.parameter_ty, predicate.clone(), offset).or_else(|| {
                    find_in_expr_offset(&lambda.result, predicate.clone(), offset.succ())
                })
            }
            ExprContents::Pi(pi) => {
                find_in_expr_offset(&pi.parameter_ty, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&pi.result, predicate.clone(), offset.succ()))
            }
            ExprContents::Apply(apply) => {
                find_in_expr_offset(&apply.function, predicate.clone(), offset)
                    .or_else(|| find_in_expr_offset(&apply.argument, predicate.clone(), offset))
            }
            _ => None,
        }
        .or_else(|| {
            // Look in the type of the expression as well.
            if let Some(ty) = &e.ty {
                find_in_expr_offset(ty, predicate, offset)
            } else {
                None
            }
        })
    }
}

/// Instantiate the first bound variable with the given substitution.
/// This will subtract one from all higher de Bruijn indices.
pub fn instantiate(e: &mut Expr, substitution: &Expr) {
    replace_in_expr(e, |e, offset| {
        if let ExprContents::Bound(Bound { index, .. }) = &e.contents {
            match index.cmp(&(DeBruijnIndex::zero() + offset)) {
                std::cmp::Ordering::Less => {
                    // The variable is bound and has index lower than the offset, so we don't change it.
                    ReplaceResult::Skip
                }
                std::cmp::Ordering::Equal => {
                    // The variable is the smallest free de Bruijn index.
                    // It is exactly the one we need to substitute.
                    ReplaceResult::ReplaceWith(substitution.clone())
                }
                std::cmp::Ordering::Greater => {
                    // This de Bruijn index must be decremented, since we just
                    // instantiated a variable below it.
                    let mut e = e.clone();
                    if let ExprContents::Bound(Bound { index, .. }) = &mut e.contents {
                        *index = index.pred();
                    } else {
                        unreachable!()
                    }
                    ReplaceResult::ReplaceWith(e)
                }
            }
        } else {
            ReplaceResult::Skip
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
    replace_in_expr(e, |e, offset| match &e.contents {
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
        if let ExprContents::Bound(Bound { index, .. }) = &e.contents {
            if *index >= DeBruijnIndex::zero() + offset {
                // The variable is free.
                let mut e = e.clone();
                if let ExprContents::Bound(Bound { index, .. }) = &mut e.contents {
                    *index = *index + shift;
                } else {
                    unreachable!()
                }
                ReplaceResult::ReplaceWith(e)
            } else {
                ReplaceResult::Skip
            }
        } else {
            ReplaceResult::Skip
        }
    })
}
