use fnodes::{parse_and_report, Location};

fn main() {
    println!(
        "{:#?}",
        parse_and_report::<Location>(
            &std::fs::read_to_string("fnodes/src/test/test.sexp").expect("Failed to read file"),
        )
    );
}
