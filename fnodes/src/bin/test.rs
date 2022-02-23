use fnodes::{expr::ExprContents, parse_and_report};

fn main() {
    println!(
        "{:#?}",
        parse_and_report::<ExprContents>(
            &std::fs::read_to_string("fnodes/src/test/test.sexp").expect("Failed to read file"),
        )
    );
}
