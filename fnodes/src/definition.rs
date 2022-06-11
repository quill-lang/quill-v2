use fcommon::Span;

use crate::{basic_nodes::Name, expr::Expr, *};

#[derive(Debug)]
pub struct DefinitionContents {
    /// The name of this definition inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    pub expr: Expr,
}

pub type Definition = Node<DefinitionContents>;

impl ListSexpr for Definition {
    const KEYWORD: Option<&'static str> = Some("def");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, infos, universe_params, expr] = force_arity(span.clone(), args)?;

        let def = Node::new(
            ctx.node_id_gen.gen(),
            span.clone(),
            DefinitionContents {
                name: Name::parse(ctx, db, name)?,
                universe_params: ListSexprWrapper::parse(ctx, db, universe_params)?,
                expr: ListSexprWrapper::parse(ctx, db, expr)?,
            },
        );
        match infos.contents {
            SexprNodeContents::Atom(_) => {
                return Err(ParseError {
                    span,
                    reason: ParseErrorReason::ExpectedList,
                })
            }
            SexprNodeContents::List(infos) => {
                for info in infos {
                    ctx.process_def_info(db, &def, info)?;
                }
            }
        }
        Ok(def)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let infos = SexprNodeContents::List(ctx.process_def_info(db, self, ctx));
        vec![
            self.contents.name.serialise(ctx, db),
            SexprNode {
                contents: infos,
                span: 0..0,
            },
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.universe_params),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.expr),
        ]
    }
}
