// Expose this either when we're running `cargo doc` or executing tests.
#[cfg(any(test, doc))]
mod test_db;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;
    use fcommon::FileReader;
    use fcommon::SourceType;
    use test_db::*;

    #[test]
    fn test_sexpr() {
        let contents = "
        (def id () (u)
            (pi (T 0) imp (sort (univn 0))
            (pi (x 0) ex (bound 0)
            (bound 0)))
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        panic!("{:#?}", db.source(source));
    }
}
