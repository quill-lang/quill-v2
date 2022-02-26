use std::sync::Arc;

use fcommon::{Dr, FileReader, Source, Str};

use crate::{
    basic_nodes::SourceSpan,
    expr::{Expr, ExprContents, ExprTy},
    parse_sexpr, ListParsableWrapper, NodeInfoContainer, SexprParsable, SexprParseContext,
};

#[salsa::query_group(SexprParserStorage)]
pub trait SexprParser: FileReader {
    fn expr_from_feather_source(&self, source: Source) -> Arc<Dr<(Expr, DefaultInfos)>>;
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

fn expr_from_feather_source(db: &dyn SexprParser, source: Source) -> Arc<Dr<(Expr, DefaultInfos)>> {
    let source_code = db.source(source);
    let s_expr = parse_sexpr(source_code.as_str());
    Arc::new(s_expr.bind(|s_expr| {
        let mut default_infos = DefaultInfos::default();
        let mut ctx = SexprParseContext::default();
        default_infos.register(&mut ctx);
        let result = ListParsableWrapper::<Expr>::parse(&mut ctx, db, s_expr).map(|x| x.0);
        let ignored = ctx.finish();
        Dr::ok(result.unwrap()).map(|expr| (expr, default_infos))
    }))
}
