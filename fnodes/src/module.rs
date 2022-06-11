use fcommon::{Span, Str};

use crate::definition::Definition;
use crate::*;

#[derive(Debug)]
pub struct ModuleContents {
    pub defs: Vec<Definition>,
}

pub type Module = Node<ModuleContents>;

impl ListSexpr for Module {
    const KEYWORD: Option<&'static str> = Some("module");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        // The first node should be the infos.
        if args.is_empty() {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::Empty,
            });
        }
        let mut module = Node::new(
            ctx.node_id_gen.gen(),
            span.clone(),
            ModuleContents { defs: Vec::new() },
        );
        match args.remove(0).contents {
            SexprNodeContents::Atom(_) => {
                return Err(ParseError {
                    span,
                    reason: ParseErrorReason::ExpectedList,
                })
            }
            SexprNodeContents::List(infos) => {
                for info in infos {
                    ctx.process_module_info(db, &module, info)?;
                }
            }
        }

        for arg in args {
            module
                .contents
                .defs
                .push(ListSexprWrapper::parse(ctx, db, arg)?)
        }

        // TODO: Check for duplicate definition names.

        Ok(module)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let infos = SexprNodeContents::List(ctx.process_module_info(db, self, ctx));
        std::iter::once(SexprNode {
            contents: infos,
            span: 0..0,
        })
        .chain(
            self.contents
                .defs
                .iter()
                .map(|def| ListSexprWrapper::serialise_into_node(ctx, db, def)),
        )
        .collect()
    }
}

impl Module {
    pub fn definition(&self, name: Str) -> Option<&Definition> {
        self.contents
            .defs
            .iter()
            .find(|def| def.contents.name.contents == name)
    }

    pub fn definition_mut(&mut self, name: Str) -> Option<&mut Definition> {
        self.contents
            .defs
            .iter_mut()
            .find(|def| def.contents.name.contents == name)
    }
}
