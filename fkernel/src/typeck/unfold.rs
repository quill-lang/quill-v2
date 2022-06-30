//! Unfolds definitions.

use fcommon::InternExt;
use fnodes::expr::{Expr, ExprContents, Inst};

use super::env::Environment;

/// Returns the unfolded definition that this [`Inst`] refers to.
/// If we could not unfold the definition, return `None`.
fn unfold_definition_core<'a>(env: &'a Environment, e: &Inst) -> Option<&'a Expr> {
    env.definitions
        .get(&e.name.to_path(env.db.up()))
        .and_then(|def| def.contents.expr.as_ref())
}

/// If the head of this expression is a definition, unfold it.
/// Returns true if we unfolded something.
/// This is sometimes called delta-reduction.
pub fn unfold_definition<'a>(env: &'a Environment, e: &mut Expr) -> bool {
    match &mut e.contents {
        ExprContents::Inst(inst) => {
            if let Some(expr) = unfold_definition_core(env, inst) {
                *e = expr.clone();
                true
            } else {
                false
            }
        }
        ExprContents::Apply(ap) => unfold_definition(env, &mut *ap.function),
        _ => false,
    }
}
