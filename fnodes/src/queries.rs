use std::sync::Arc;

use fcommon::{Dr, FileReader, Label, LabelType, Report, ReportKind, Source, Str};

use crate::{
    basic_nodes::{QualifiedName, SourceSpan},
    expr::{ExprContents, ExprTy},
    parse_sexpr_from_string, ListSexprWrapper, Module, NodeIdGenerator, NodeInfoContainer,
    SexprNode, SexprParsable, SexprParseContext,
};

#[salsa::query_group(SexprParserStorage)]
pub trait SexprParser: FileReader {
    fn parse_sexpr(&self, source: Source) -> Dr<Arc<SexprNode>>;
    fn module_from_feather_source(&self, source: Source) -> Dr<Arc<ModuleParseResult>>;
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

/// Represents the result of a module parse operation.
/// `I` is expected to be a type containing node infos.
#[derive(Debug, PartialEq, Eq)]
pub struct ModuleParseResult<I = DefaultInfos> {
    pub module: Arc<Module>,
    /// The node ID generator associated with the nodes in the returned module.
    pub node_id_gen: NodeIdGenerator,
    pub infos: I,
}

#[tracing::instrument(level = "debug")]
fn parse_sexpr(db: &dyn SexprParser, source: Source) -> Dr<Arc<SexprNode>> {
    db.source(source)
        .as_deref()
        .bind(|source_code| parse_sexpr_from_string(source, source_code))
        .map(Arc::new)
}

#[tracing::instrument(level = "debug")]
fn module_from_feather_source(db: &dyn SexprParser, source: Source) -> Dr<Arc<ModuleParseResult>> {
    db.parse_sexpr(source)
        .as_deref()
        .bind(|s_expr| {
            let mut default_infos = DefaultInfos::default();
            let mut ctx = SexprParseContext::default();
            default_infos.register(&mut ctx);
            let result: Dr<_> = ListSexprWrapper::<Module>::parse(&mut ctx, db, s_expr.clone())
                .map_err(|x| x.into_report(source))
                .map(Arc::new)
                .into();
            let ctx_result = ctx.finish();
            result.bind(|module| {
                let result = ModuleParseResult {
                    module,
                    node_id_gen: ctx_result.node_id_gen,
                    infos: default_infos,
                };

                let note = [
                    ("expr", ctx_result.expr_ignored_keywords),
                    ("comp", ctx_result.component_ignored_keywords),
                    ("name", ctx_result.name_ignored_keywords),
                    ("module", ctx_result.module_ignored_keywords),
                    ("def", ctx_result.def_ignored_keywords),
                ]
                .into_iter()
                .filter_map(|(name, kwds)| {
                    if !kwds.is_empty() {
                        Some(format!(
                            "{} keywords: {}",
                            name,
                            kwds.iter().cloned().collect::<Vec<_>>().join(", ")
                        ))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join("; ");

                if note.is_empty() {
                    Dr::ok(result)
                } else {
                    let note = format!("ignored {}", note);
                    Dr::ok_with(
                        result,
                        Report::new_in_file(ReportKind::Warning, source)
                            .with_message("some S-expression infos were not parsed")
                            .with_label(Label::new(source, 0..0, LabelType::Note))
                            .with_note(note),
                    )
                }
            })
        })
        .map(Arc::new)
}

pub trait SexprParserExt: SexprParser {
    fn qualified_name_to_path(&self, qn: &QualifiedName) -> fcommon::Path {
        self.intern_path_data(fcommon::PathData(
            qn.0.iter().map(|name| name.contents).collect(),
        ))
    }
}
impl<T> SexprParserExt for T where T: SexprParser {}
