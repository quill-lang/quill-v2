use std::sync::Arc;

use fcommon::{Dr, FileReader, Source, Str};

use crate::{
    basic_nodes::SourceSpan,
    expr::{Expr, ExprContents, ExprTy},
    parse_sexpr, ListParsableWrapper, NodeIdGenerator, NodeInfoContainer, SexprParsable,
    SexprParseContext,
};

#[salsa::query_group(SexprParserStorage)]
pub trait SexprParser: FileReader {
    fn expr_from_feather_source(&self, source: Source) -> Arc<Dr<ExprParseResult>>;
}

/// A set of infos that may be useful to any feather compiler component.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct DefaultInfos {
    pub expr_at: NodeInfoContainer<ExprContents, SourceSpan>,
    pub expr_ty: NodeInfoContainer<ExprContents, ExprTy>,
    pub name_at: NodeInfoContainer<Str, SourceSpan>,
}

impl DefaultInfos {
    /// Register all infos in the parse context.
    pub fn register<'a>(&'a mut self, ctx: &mut SexprParseContext<'a>) {
        ctx.register_expr_info(&mut self.expr_at);
        ctx.register_expr_info(&mut self.expr_ty);
        ctx.register_name_info(&mut self.name_at);
    }
}

/// Represents the result of an expression parse operation.
/// `I` is expected to be a type containing node infos.
#[derive(Debug, PartialEq, Eq)]
pub struct ExprParseResult<I = DefaultInfos> {
    pub expr: Expr,
    /// The node ID generator associated with the nodes in the returned expression.
    pub node_id_gen: NodeIdGenerator,
    pub infos: I,
}

fn expr_from_feather_source(db: &dyn SexprParser, source: Source) -> Arc<Dr<ExprParseResult>> {
    let source_code = db.source(source);
    let s_expr = parse_sexpr(source, source_code.as_str());
    Arc::new(s_expr.bind(|s_expr| {
        let mut default_infos = DefaultInfos::default();
        let mut ctx = SexprParseContext::default();
        default_infos.register(&mut ctx);
        let result: Dr<_> = ListParsableWrapper::<Expr>::parse(&mut ctx, db, s_expr)
            .map(|x| x.0)
            .map_err(|x| x.into_report(source))
            .into();
        let ctx_result = ctx.finish();
        result.map(|expr| ExprParseResult {
            expr,
            node_id_gen: ctx_result.node_id_gen,
            infos: default_infos,
        })
    }))
}