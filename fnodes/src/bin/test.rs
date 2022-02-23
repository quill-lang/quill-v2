use fnodes::{expr::Expr, parse_and_report};

fn main() {
    println!(
        "{:#?}",
        parse_and_report::<Expr>(
            &std::fs::read_to_string("fnodes/src/test/test.sexp").expect("Failed to read file"),
        )
    );
}
