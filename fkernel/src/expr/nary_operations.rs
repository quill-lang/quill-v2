//! Provides utilities for working with n-ary functions, even though
//! function currying makes all functions behave like they are unary.

use fnodes::{basic_nodes::Provenance, expr::*};

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

/// Suppose that this expression is an n-ary function application, where n is zero or a positive integer.
/// Then, this function returns the [leftmost_function] of this expression, and the list of [apply_args]
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
