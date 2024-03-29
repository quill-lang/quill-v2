//! Provides utilities for working with n-ary functions, even though
//! function currying makes all functions behave like they are unary.

use fnodes::{basic_nodes::Provenance, expr::*};

use super::{abstract_lambda, abstract_pi};

/// If this expression is a function application, return the leftmost function in the call chain.
/// For example, applying this function to `foo 1 2 3` returns `foo`,
/// and applying it to `(foo bar) 1 2 3` returns `foo bar`.
/// If this is not a function application, we interpret the expression as a nullary function,
/// and return the whole expression.
pub fn leftmost_function(e: &Expr) -> &Expr {
    if let ExprContents::Apply(apply) = &e.contents {
        leftmost_function(&apply.function)
    } else {
        e
    }
}

/// If this is a function application, return the list of arguments applied to the
/// [leftmost_function] of the expression.
/// Applying this function to `foo 1 2 3` returns `[1, 2, 3]`.
/// If this is not a function application, return `[]`.
pub fn apply_args(e: &Expr) -> Vec<&Expr> {
    if let ExprContents::Apply(apply) = &e.contents {
        let mut result = apply_args(&apply.function);
        result.push(&apply.argument);
        result
    } else {
        Vec::new()
    }
}

/// See [`apply_args`].
pub fn apply_args_mut(mut e: &mut Expr) -> Vec<&mut Expr> {
    let mut result = Vec::new();
    loop {
        if let ExprContents::Apply(apply) = &mut e.contents {
            e = &mut *apply.function;
            result.push(&mut *apply.argument);
        } else {
            result.reverse();
            return result;
        }
    }
}

/// Returns the arguments, in order, to a [`Pi`].
/// Discards the return value.
pub fn pi_args(mut e: &Expr, meta_gen: &mut MetavariableGenerator) -> Vec<LocalConstant> {
    let mut result = Vec::new();
    while let ExprContents::Pi(pi) = &e.contents {
        e = &pi.result;
        result.push(pi.generate_local(meta_gen));
    }
    result
}


/// Suppose that this expression is an n-ary function application, where n is zero or a positive integer.
/// Then, this function returns the [`leftmost_function`] of this expression, and the list of [`apply_args`]
/// that were applied to it.
/// Applying this function to `foo 1 2 3` returns `(foo, [1, 2, 3])`.
pub fn destructure_as_nary_application(e: &Expr) -> (&Expr, Vec<&Expr>) {
    (leftmost_function(e), apply_args(e))
}

/// Creates an n-ary function application chain with the given provenance data from the given function and arguments.
pub fn create_nary_application(
    function: Expr,
    arguments: impl Iterator<Item = Expr>,
    provenance: &Provenance,
) -> Expr {
    arguments.fold(function, |func, arg| {
        Expr::new_with_provenance(
            provenance,
            ExprContents::Apply(Apply {
                function: Box::new(func),
                argument: Box::new(arg),
            }),
        )
    })
}

/// Creates a [`Lambda`] expression that can be evaluated with the given local constants in `arguments`
/// to produce the expression `result`.
pub fn abstract_nary_lambda(
    locals: impl DoubleEndedIterator<Item = LocalConstant>,
    result: Expr,
    provenance: &Provenance,
) -> Expr {
    locals.rev().fold(result, |result, local| {
        Expr::new_with_provenance(
            provenance,
            ExprContents::Lambda(abstract_lambda(local, result)),
        )
    })
}

/// Creates a [`Pi`] expression that can be evaluated with the given local constants in `arguments`
/// to produce the expression `result`.
pub fn abstract_nary_pi(
    locals: impl DoubleEndedIterator<Item = LocalConstant>,
    result: Expr,
    provenance: &Provenance,
) -> Expr {
    locals.rev().fold(result, |result, local| {
        Expr::new_with_provenance(provenance, ExprContents::Pi(abstract_pi(local, result)))
    })
}
