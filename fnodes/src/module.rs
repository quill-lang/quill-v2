use fcommon::{Source, Span, Str};

use crate::basic_nodes::Provenance;
use crate::definition::Definition;
use crate::inductive::Inductive;
use crate::*;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ModuleContents {
    pub defs: Vec<Definition>,
    pub inductives: Vec<Inductive>,
}

#[derive(PartialEq, Eq, Hash)]
pub struct Module {
    /// The origin of the module in code.
    provenance: Provenance,
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
            contents: ModuleContents {
                defs: Vec::new(),
                inductives: Vec::new(),
            },
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
                    .inductives
                    .push(ListSexprWrapper::parse(db, source, arg)?)
            } else {
                module
                    .contents
                    .defs
                    .push(ListSexprWrapper::parse(db, source, arg)?)
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
            .defs
            .iter()
            .map(|def| ListSexprWrapper::serialise_into_node(db, def))
            // )
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
