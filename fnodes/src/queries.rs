use std::sync::Arc;

use fcommon::{Dr, FileReader, Source};
use upcast::{Upcast, UpcastFrom};

use crate::{
    basic_nodes::QualifiedName, module::Module, parse_sexpr_from_string, ListSexprWrapper,
    SexprNode, SexprParsable,
};

#[salsa::query_group(SexprParserStorage)]
pub trait SexprParser: FileReader {
    fn parse_sexpr(&self, source: Source) -> Dr<Arc<SexprNode>>;
    fn module_from_feather_source(&self, source: Source) -> Dr<Arc<Module>>;
}

#[tracing::instrument(level = "debug")]
fn parse_sexpr(db: &dyn SexprParser, source: Source) -> Dr<Arc<SexprNode>> {
    db.source(source)
        .as_deref()
        .bind(|source_code| parse_sexpr_from_string(source, source_code))
        .map(Arc::new)
}

#[tracing::instrument(level = "debug")]
fn module_from_feather_source(db: &dyn SexprParser, source: Source) -> Dr<Arc<Module>> {
    db.parse_sexpr(source).as_deref().bind(|s_expr| {
        ListSexprWrapper::<Module>::parse(db, source, s_expr.clone())
            .map_err(|x| x.into_report(source))
            .map(Arc::new)
            .into()
    })
}

pub trait SexprParserExt: SexprParser + Upcast<dyn SexprParser> {
    fn qualified_name_to_path(&self, qn: &QualifiedName) -> fcommon::Path {
        self.intern_path_data(fcommon::PathData(
            qn.segments.iter().map(|name| name.contents).collect(),
        ))
    }
}
impl<'a, T: SexprParser + 'a> UpcastFrom<T> for dyn SexprParser + 'a {
    fn up_from(value: &T) -> &(dyn SexprParser + 'a) {
        value
    }
    fn up_from_mut(value: &mut T) -> &mut (dyn SexprParser + 'a) {
        value
    }
}
impl<T> SexprParserExt for T where T: SexprParser + 'static {}
