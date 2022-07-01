//! Unfolds definitions.

use fcommon::InternExt;
use fnodes::expr::{Expr, ExprContents, Inst};

use super::env::{DefinitionHeight, Environment, ReducibilityHints};

/// Returns a number if the head of this expression is a definition that we can unfold.
/// Intuitively, the number returned is higher for more complicated definitions.
pub fn head_definition_height<'a>(env: &'a Environment, e: &Expr) -> Option<DefinitionHeight> {
    match &e.contents {
        ExprContents::Inst(inst) => env
            .definitions
            .get(&inst.name.to_path(env.db.up()))
            .and_then(|def| match def.reducibility {
                ReducibilityHints::Regular { height } => Some(height),
                ReducibilityHints::Opaque => None,
            }),
        ExprContents::Apply(ap) => head_definition_height(env, &*ap.function),
        _ => None,
    }
}

/// Returns the unfolded definition that this [`Inst`] refers to.
/// If we could not unfold the definition, return `None`.
fn unfold_definition_core<'a>(env: &'a Environment, e: &Inst) -> Option<&'a Expr> {
    env.definitions
        .get(&e.name.to_path(env.db.up()))
        .and_then(|def| def.def.contents.expr.as_ref())
}

/// If the head of this expression is a definition, unfold it,
/// even if it is marked as [`ReducibilityHints::Opaque`].
/// Returns true if we unfolded something.
/// This is sometimes called delta-reduction.
/// This will always return true if [`can_unfold_definition`] returned a [`Some`] value.
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
