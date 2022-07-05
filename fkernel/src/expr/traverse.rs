//! Utilities for traversing the expression tree for things like find-and-replace operations.

use std::{borrow::BorrowMut, cell::Cell};

use fcommon::Str;
use fnodes::{
    basic_nodes::{DeBruijnIndex, DeBruijnOffset, Name},
    expr::*,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    typeck::{definition_height, DefinitionHeight, Environment},
    universe::instantiate_universe,
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
                ExprContents::LocalConstant(local) => {
                    replace_in_expr_offset(&mut local.metavariable.ty, replace_fn.clone(), offset);
                }
                ExprContents::Metavariable(var) => {
                    replace_in_expr_offset(&mut var.ty, replace_fn.clone(), offset);
                }
                ExprContents::Let(let_expr) => {
                    replace_in_expr_offset(&mut let_expr.to_assign, replace_fn.clone(), offset);
                    replace_in_expr_offset(&mut let_expr.to_assign_ty, replace_fn.clone(), offset);
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
            ExprContents::LocalConstant(local) => {
                find_in_expr_offset(&local.metavariable.ty, predicate.clone(), offset)
            }
            ExprContents::Metavariable(var) => {
                find_in_expr_offset(&var.ty, predicate.clone(), offset)
            }
            ExprContents::Let(let_expr) => {
                find_in_expr_offset(&let_expr.to_assign, predicate.clone(), offset).or_else(|| {
                    find_in_expr_offset(&let_expr.to_assign_ty, predicate.clone(), offset).or_else(
                        || find_in_expr_offset(&let_expr.body, predicate.clone(), offset.succ()),
                    )
                })
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
    let mut height = Cell::new(0);
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
        if let ExprContents::Bound(Bound { index, .. }) = &e.contents {
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

/// Create a lambda expression where the parameter is the given local constant.
pub fn abstract_lambda(local: LocalConstant, mut return_type: Expr) -> Lambda {
    replace_in_expr(&mut return_type, |e, offset| {
        if let ExprContents::LocalConstant(inner_local) = &e.contents {
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
        } else {
            ReplaceResult::Skip
        }
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
    replace_in_expr(&mut return_type, |e, offset| {
        if let ExprContents::LocalConstant(inner_local) = &e.contents {
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
        } else {
            ReplaceResult::Skip
        }
    });
    Pi {
        parameter_name: local.name,
        binder_annotation: local.binder_annotation,
        parameter_ty: local.metavariable.ty,
        result: Box::new(return_type),
    }
}
