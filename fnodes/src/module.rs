use fcommon::{Span, Str};

use crate::*;
use crate::{basic_nodes::Name, expr::Expr};

#[derive(Debug)]
pub struct ModuleContents {
    pub defs: Vec<Definition>,
}

pub type Module = Node<ModuleContents>;

impl SexprListParsable for Module {
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
                .push(ListParsableWrapper::parse(ctx, db, arg)?.0)
        }

        // TODO: Check for duplicate definition names.

        Ok(module)
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

#[derive(Debug)]
pub struct DefinitionContents {
    pub name: Name,
    pub expr: Expr,
}

pub type Definition = Node<DefinitionContents>;

impl SexprListParsable for Definition {
    const KEYWORD: Option<&'static str> = Some("def");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, infos, expr] = force_arity(span.clone(), args)?;

        let def = Node::new(
            ctx.node_id_gen.gen(),
            span.clone(),
            DefinitionContents {
                name: Name::parse(ctx, db, name)?,
                expr: ListParsableWrapper::parse(ctx, db, expr)?.0,
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
}
