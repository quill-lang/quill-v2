use fnodes::{
    expr::{Expr, ExprAt, ExprContents},
    parse_and_report, NodeInfoContainer, NodeInfoInserters,
};

fn main() {
    let mut infos = NodeInfoInserters::default();
    let mut expr_at = NodeInfoContainer::<ExprContents, ExprAt>::new();
    infos.register_expr_info(&mut expr_at);
    println!(
        "{:#?}",
        parse_and_report::<Expr>(
            &mut infos,
            &std::fs::read_to_string("fnodes/src/test/test.sexp").expect("Failed to read file"),
        )
    );
    println!("ignored {:#?}", infos.finish());
    println!("spans {:#?}", expr_at);
}
