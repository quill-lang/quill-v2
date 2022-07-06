//! Converts expressions to weak head normal form.
//!
//! Conversion rules: <https://coq.inria.fr/refman/language/core/conversion.html>

use fnodes::expr::{Expr, ExprContents};

use crate::expr::instantiate;

use super::{env::Environment, unfold::unfold_definition};

/// Reduces an expression to weak head normal form.
pub fn to_weak_head_normal_form(env: &Environment, e: &mut Expr) {
    loop {
        whnf_core(e);
        if !unfold_definition(env, e) {
            break;
        }
    }
}

/// Does not perform delta reduction.
/// Returns true if any normalisation was performed.
/// TODO: Lean's kernel performs more normalisation (using `norm_ext`). Is this necessary in our case?
fn whnf_core(e: &mut Expr) {
    match &mut e.contents {
        ExprContents::Let(let_expr) => {
            // We substitute the value into the body of the let expression, then continue to evaluate the expression.
            // This is called zeta-reduction.
            let mut body = std::mem::replace(&mut let_expr.body, Box::new(Expr::dummy()));
            instantiate(&mut body, &let_expr.to_assign);
            *e = *body;
            whnf_core(e);
        }
        ExprContents::Apply(ap) => {
            // Try to reduce the function to weak head normal form first.
            whnf_core(&mut ap.function);
            if let ExprContents::Lambda(lam) = &mut ap.function.contents {
                // If the function is a lambda, we can apply a beta-reduction to expand the lambda.
                let mut result = std::mem::replace(&mut lam.result, Box::new(Expr::dummy()));
                instantiate(&mut result, &ap.argument);
                *e = *result;
                whnf_core(e);
            }
        }
        _ => {}
    }
}
