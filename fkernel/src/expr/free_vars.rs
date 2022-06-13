//! Tests whether expressions have free variables or are closed.

use fnodes::{basic_nodes::DeBruijnIndex, expr::*};

/// All de Bruijn indices used by this expression are less than the return value.
/// For instance, if the expression is `#0`, we return `#1`.
/// If the expression is `let x = _ in #0`, we return `#0`, because the inner `#0` refers to `x`.
/// If the expression is `let x = _ in #1`, we return `#0`, because the `#1` inside the `let` body
/// refers to what we would call `#0` from outside the expression.
fn first_free_variable_index(e: &Expr) -> DeBruijnIndex {
    let contents = match &e.contents {
        ExprContents::Bound(Bound(idx)) => idx.succ(),
        ExprContents::Inst(_) => DeBruijnIndex::zero(),
        ExprContents::Let(let_expr) => std::cmp::max(
            first_free_variable_index(&let_expr.to_assign),
            first_free_variable_index(&let_expr.body).pred(),
        ),
        ExprContents::Lambda(lambda) => std::cmp::max(
            first_free_variable_index(&lambda.parameter_ty),
            first_free_variable_index(&lambda.result).pred(),
        ),
        ExprContents::Pi(pi) => std::cmp::max(
            first_free_variable_index(&pi.parameter_ty),
            first_free_variable_index(&pi.result).pred(),
        ),
        ExprContents::Apply(apply) => std::cmp::max(
            first_free_variable_index(&apply.function),
            first_free_variable_index(&apply.argument),
        ),
        ExprContents::Sort(_) => DeBruijnIndex::zero(),
        ExprContents::Metavariable(_) => DeBruijnIndex::zero(),
        ExprContents::LocalConstant(_) => DeBruijnIndex::zero(),
    };
    if let Some(ty) = &e.ty {
        std::cmp::max(contents, first_free_variable_index(ty))
    } else {
        contents
    }
}

/// An expression is called *closed* if it contains no free variables.
/// In our context, an expression is closed if all de Bruijn indices refer inside the expression.
/// This doesn't track metavariables, and after a substitution, it's possible that closed expressions
/// now contain free variables.
/// The opposite of [`has_free_variables`].
pub fn closed(e: &Expr) -> bool {
    first_free_variable_index(e) == DeBruijnIndex::zero()
}

/// An expression has *free variables* if there are any de Bruijn indices pointing outside the expression.
/// The opposite of [`closed`].
pub fn has_free_variables(e: &Expr) -> bool {
    !closed(e)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::test_db::*;
    use fcommon::SourceType;
    use fnodes::{expr::ExprPrinter, module::Module, SexprParser};

    #[test]
    fn test_closed() {
        let contents = "
        (module
            ()
            (def id (u)
                (lam T imp (sort (univn 0))
                (lam x ex (bound 0)
                (bound 0)))
            )
            (def id_mistake (u)
                (lam T imp (sort (univn 0))
                (lam x ex (bound 0)
                (bound 1)))
            )
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        let module: Arc<Module> = db.module_from_feather_source(source).unwrap();
        for def in &module.contents.defs {
            let e = &def.contents.expr;
            if !closed(e) {
                panic!("{}", ExprPrinter::new(&db).print(e));
            }
        }
    }

    #[test]
    fn test_not_closed() {
        let contents = "
        (module
            ()
            (def id_broken (u)
                (lam T imp (sort (univn 0))
                (lam x ex (bound 0)
                (bound 2)))
            )
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        let module: Arc<Module> = db.module_from_feather_source(source).unwrap();
        for def in &module.contents.defs {
            let e = &def.contents.expr;
            if closed(e) {
                panic!("{}", ExprPrinter::new(&db).print(e));
            }
        }
    }
}
