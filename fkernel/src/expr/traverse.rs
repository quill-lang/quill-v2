//! Utilities for traversing the expression tree for things like find-and-replace operations.

use fnodes::{
    basic_nodes::{DeBruijnIndex, DeBruijnOffset},
    expr::*,
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
///
/// Replacement occurs in types of expressions as well as their values.
fn replace_in_expr(e: &mut Expr, replace_fn: impl Fn(&Expr, DeBruijnOffset) -> ReplaceResult) {
    replace_in_expr_offset(e, replace_fn, DeBruijnOffset::zero())
}

/// Like [`replace_in_expr`] but keeps track of sub-expression de Bruijn index offsets.
fn replace_in_expr_offset(
    e: &mut Expr,
    replace_fn: impl Fn(&Expr, DeBruijnOffset) -> ReplaceResult,
    offset: DeBruijnOffset,
) {
    // Invoke the replacement function.
    match replace_fn(e, offset) {
        ReplaceResult::Skip => {
            // Traverse the sub-expressions of `e`.
            match &mut e.contents {
                ExprContents::Let(let_expr) => {
                    replace_in_expr_offset(
                        &mut let_expr.to_assign,
                        // To avoid requiring `Clone` on `replace_fn`, we can just make an inner function that calls `replace_fun`.
                        |a, b| replace_fn(a, b),
                        offset,
                    );
                    replace_in_expr_offset(
                        &mut let_expr.body,
                        |a, b| replace_fn(a, b),
                        offset.succ(),
                    );
                }
                ExprContents::Lambda(lambda) => {
                    replace_in_expr_offset(
                        &mut lambda.parameter_ty,
                        |a, b| replace_fn(a, b),
                        offset,
                    );
                    replace_in_expr_offset(
                        &mut lambda.result,
                        |a, b| replace_fn(a, b),
                        offset.succ(),
                    );
                }
                ExprContents::Pi(pi) => {
                    replace_in_expr_offset(&mut pi.parameter_ty, |a, b| replace_fn(a, b), offset);
                    replace_in_expr_offset(&mut pi.result, |a, b| replace_fn(a, b), offset.succ());
                }
                ExprContents::Apply(apply) => {
                    replace_in_expr_offset(&mut apply.function, |a, b| replace_fn(a, b), offset);
                    replace_in_expr_offset(&mut apply.argument, |a, b| replace_fn(a, b), offset);
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
fn find_in_expr(e: &Expr, predicate: impl Fn(&Expr, DeBruijnOffset) -> bool) -> Option<&Expr> {
    find_in_expr_offset(e, predicate, DeBruijnOffset::zero())
}

/// Like [`find_in_expr`] but keeps track of sub-expression de Bruijn index offsets.
fn find_in_expr_offset(
    e: &Expr,
    predicate: impl Fn(&Expr, DeBruijnOffset) -> bool,
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
                    |a, b| predicate(a, b),
                    offset,
                )
                .or_else(|| {
                    find_in_expr_offset(&let_expr.body, |a, b| predicate(a, b), offset.succ())
                })
            }
            ExprContents::Lambda(lambda) => {
                find_in_expr_offset(&lambda.parameter_ty, |a, b| predicate(a, b), offset).or_else(
                    || find_in_expr_offset(&lambda.result, |a, b| predicate(a, b), offset.succ()),
                )
            }
            ExprContents::Pi(pi) => {
                find_in_expr_offset(&pi.parameter_ty, |a, b| predicate(a, b), offset).or_else(
                    || find_in_expr_offset(&pi.result, |a, b| predicate(a, b), offset.succ()),
                )
            }
            ExprContents::Apply(apply) => {
                find_in_expr_offset(&apply.function, |a, b| predicate(a, b), offset).or_else(|| {
                    find_in_expr_offset(&apply.argument, |a, b| predicate(a, b), offset)
                })
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
        if let ExprContents::Bound(Bound(idx)) = &e.contents {
            match idx.cmp(&(DeBruijnIndex::zero() + offset)) {
                std::cmp::Ordering::Less => {
                    // The variable is free.
                    ReplaceResult::Skip
                }
                std::cmp::Ordering::Equal => {
                    // The variable is bound at exactly the offset level.
                    // It is exactly the one we need to substitute.
                    ReplaceResult::ReplaceWith(substitution.clone())
                }
                std::cmp::Ordering::Greater => {
                    // This de Bruijn index must be decremented, since we just
                    // instantiated a variable below it.
                    let mut e = e.clone();
                    if let ExprContents::Bound(Bound(idx)) = &mut e.contents {
                        *idx = idx.pred();
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
