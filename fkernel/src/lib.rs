// Expose this either when we're running `cargo doc` or executing tests.
#[cfg(any(test, doc))]
mod test_db;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;
    use fcommon::SourceType;
    use fnodes::expr::ToValue;
    use fnodes::{expr::ValuePrinter, SexprParser};
    use test_db::*;

    #[test]
    fn test_sexpr() {
        let contents = "
        (module
            ()
            (def id () (u)
                (lam (T 0) imp (sort (univn 0))
                (lam (x 0) ex (bound 0)
                (bound 0)))
            )
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        let module = db.module_from_feather_source(source).unwrap();
        let mut v = ValuePrinter::new(&db);
        panic!(
            "{}",
            v.print(&module.module.contents.defs[0].contents.expr.to_value(&db))
        );
    }
}
