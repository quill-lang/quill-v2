use fnodes::{
    basic_nodes::SourceSpan,
    expr::{Expr, ExprContents, ExprTy},
    parse_and_report, NodeInfoContainer, NodeInfoInserters,
};
use lasso::Spur;

fn main() {
    let mut infos = NodeInfoInserters::default();
    let mut expr_at = NodeInfoContainer::<ExprContents, SourceSpan>::new();
    infos.register_expr_info(&mut expr_at);
    let mut expr_ty = NodeInfoContainer::<ExprContents, ExprTy>::new();
    infos.register_expr_info(&mut expr_ty);
    let mut name_at = NodeInfoContainer::<Spur, SourceSpan>::new();
    infos.register_name_info(&mut name_at);
    println!(
        "{:#?}",
        parse_and_report::<Expr>(
            &mut infos,
            &std::fs::read_to_string("fnodes/src/test/test.sexp").expect("Failed to read file"),
        )
    );
    println!("ignored {:#?}", infos.finish());
    println!("exprs {:#?}", expr_at);
    println!("names {:#?}", name_at);
}
