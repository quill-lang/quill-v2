use fcommon::{Source, Span, Str};

use crate::basic_nodes::Provenance;
use crate::definition::Definition;
use crate::inductive::Inductive;
use crate::*;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ModuleContents {
    pub items: Vec<Item>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Item {
    Definition(Definition),
    Inductive(Inductive),
}

#[derive(PartialEq, Eq, Hash)]
pub struct Module {
    /// The origin of the module in code.
    pub provenance: Provenance,
    /// The contents of the module.
    pub contents: ModuleContents,
}

impl std::fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "module {:?}:\n{:?}", self.provenance, self.contents)
    }
}

impl ListSexpr for Module {
    const KEYWORD: Option<&'static str> = Some("module");

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
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
        let mut module = Module {
            provenance: Provenance::Sexpr {
                source,
                span: span.clone(),
            },
            contents: ModuleContents { items: Vec::new() },
        };
        match args.remove(0).contents {
            SexprNodeContents::Atom(_) => {
                return Err(ParseError {
                    span,
                    reason: ParseErrorReason::ExpectedList,
                })
            }
            SexprNodeContents::List(infos) => {
                for info in infos {
                    // ctx.process_module_info(db, &module, info)?;
                }
            }
        }

        for arg in args {
            let keyword = find_keyword_from_list(&arg);
            if matches!(keyword.as_deref(), Ok("ind")) {
                module
                    .contents
                    .items
                    .push(Item::Inductive(ListSexprWrapper::parse(db, source, arg)?))
            } else {
                module
                    .contents
                    .items
                    .push(Item::Definition(ListSexprWrapper::parse(db, source, arg)?))
            }
        }

        // TODO: Check for duplicate definition names.

        Ok(module)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: node infos
        // let infos = SexprNodeContents::List(ctx.process_module_info(db, self, ctx));
        // std::iter::once(SexprNode {
        //     contents: infos,
        //     span: 0..0,
        // })
        // .chain(
        self.contents
            .items
            .iter()
            .map(|item| match item {
                Item::Definition(def) => ListSexprWrapper::serialise_into_node(db, def),
                Item::Inductive(ind) => ListSexprWrapper::serialise_into_node(db, ind),
            })
            // )
            .collect()
    }
}

impl Module {
    pub fn definition(&self, name: Str) -> Option<&Definition> {
        self.contents.items.iter().find_map(|item| {
            if let Item::Definition(def) = item {
                if def.contents.name.contents == name {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    pub fn definition_mut(&mut self, name: Str) -> Option<&mut Definition> {
        self.contents.items.iter_mut().find_map(|item| {
            if let Item::Definition(def) = item {
                if def.contents.name.contents == name {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }
}
