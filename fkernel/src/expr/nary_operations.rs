//! Provides utilities for working with n-ary functions, even though
//! function currying makes all functions behave like they are unary.

use fnodes::expr::*;

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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::test_db::*;
    use fcommon::Intern;
    use fcommon::SourceType;
    use fnodes::{basic_nodes::DeBruijnIndex, module::Module, SexprParser};

    const MODULE: &str = "
    (module
        ()
        (def nullary ()
            (bound 0)
        )
        (def call_chain ()
            (ap (ap (bound 0) (bound 1)) (bound 2))
        )
        (def call_chain2 ()
            (ap (ap (bound 0) (bound 1)) (ap (bound 2) (bound 3)))
        )
    )
    ";

    #[test]
    fn test_leftmost_function() {
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, MODULE);
        let module: Arc<Module> = db.module_from_feather_source(source).unwrap();
        for def in &module.contents.defs {
            let e = &def.contents.expr;
            assert_eq!(
                leftmost_function(e).contents,
                ExprContents::Bound(Bound(DeBruijnIndex::zero()))
            );
        }
    }

    #[test]
    fn test_apply_args() {
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, MODULE);
        let module: Arc<Module> = db.module_from_feather_source(source).unwrap();

        let nullary = module
            .definition(db.intern_string_data("nullary".to_string()))
            .unwrap();
        assert_eq!(apply_args(&nullary.contents.expr), Vec::<&Expr>::new());

        let call_chain = module
            .definition(db.intern_string_data("call_chain".to_string()))
            .unwrap();
        let call_chain_args = apply_args(&call_chain.contents.expr);
        assert_eq!(call_chain_args.len(), 2);
        assert_eq!(
            call_chain_args[0].contents,
            ExprContents::Bound(Bound(DeBruijnIndex::zero().succ()))
        );
        assert_eq!(
            call_chain_args[1].contents,
            ExprContents::Bound(Bound(DeBruijnIndex::zero().succ().succ()))
        );

        let call_chain2 = module
            .definition(db.intern_string_data("call_chain2".to_string()))
            .unwrap();
        let call_chain2_args = apply_args(&call_chain2.contents.expr);
        assert_eq!(call_chain2_args.len(), 2);
        assert_eq!(
            call_chain2_args[0].contents,
            ExprContents::Bound(Bound(DeBruijnIndex::zero().succ()))
        );
    }
}
