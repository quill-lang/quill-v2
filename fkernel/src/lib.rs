// Expose this either when we're running `cargo doc` or executing tests.
#[cfg(any(test, doc))]
mod test_db;

pub mod expr;

#[cfg(test)]
mod tests {
    use super::*;
    use fcommon::SourceType;
    use fnodes::{expr::ValuePrinter, SexprParser};
    use test_db::*;

    #[test]
    fn test_sexpr() {
        let contents = "
        (module
            ()
            (def id (u)
                (lam T imp (sort (univn 0))
                (lam x ex (bound 0)
                (bound 0)))
            )
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        let module = db.module_from_feather_source(source).unwrap();
        let mut v = ValuePrinter::new(&db);
        panic!("{}", v.print(&module.contents.defs[0].contents.expr));
    }
}
