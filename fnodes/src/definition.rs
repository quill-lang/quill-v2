use fcommon::{Source, Span};

use crate::{
    basic_nodes::{Name, Provenance},
    expr::Expr,
    *,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefinitionContents {
    /// The name of this definition inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the definition.
    pub ty: Expr,
    /// The value of the definition.
    pub expr: Option<Expr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Definition {
    /// The origin of the expression.
    pub provenance: Provenance,
    /// The actual contents of this expression.
    pub contents: DefinitionContents,
}

impl std::fmt::Debug for Definition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.provenance, self.contents)
    }
}

impl ListSexpr for Definition {
    const KEYWORD: Option<&'static str> = Some("def");

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let def = match <Vec<_> as TryInto<[_; 3]>>::try_into(args) {
            Ok([name, universe_params, ty]) => Definition {
                provenance: Provenance::Sexpr {
                    source,
                    span,
                },
                contents: DefinitionContents {
                    name: Name::parse(db, source, name)?,
                    universe_params: ListSexprWrapper::parse(db, source, universe_params)?,
                    ty: ListSexprWrapper::parse(db, source, ty)?,
                    expr: None,
                },
            },
            Err(args) => {
                let [name, /* infos, */ universe_params, ty, expr] = force_arity(span.clone(), args)?;

                Definition {
                    provenance: Provenance::Sexpr {
                        source,
                        span,
                    },
                    contents: DefinitionContents {
                        name: Name::parse(db, source, name)?,
                        universe_params: ListSexprWrapper::parse(db, source, universe_params)?,
                        ty: ListSexprWrapper::parse(db, source, ty)?,
                        expr: Some(ListSexprWrapper::parse(db, source, expr)?),
                    },
                }
            }
        };
        // match infos.contents {
        //     SexprNodeContents::Atom(_) => {
        //         return Err(ParseError {
        //             span,
        //             reason: ParseErrorReason::ExpectedList,
        //         })
        //     }
        //     SexprNodeContents::List(infos) => {
        //         for info in infos {
        //             ctx.process_def_info(db, &def, info)?;
        //         }
        //     }
        // }
        Ok(def)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: node infos
        // let infos = SexprNodeContents::List(ctx.process_def_info(db, self, ctx));
        if let Some(expr) = &self.contents.expr {
            vec![
                self.contents.name.serialise(db),
                ListSexprWrapper::serialise_into_node(db, &self.contents.universe_params),
                ListSexprWrapper::serialise_into_node(db, &self.contents.ty),
                ListSexprWrapper::serialise_into_node(db, expr),
            ]
        } else {
            vec![
                self.contents.name.serialise(db),
                ListSexprWrapper::serialise_into_node(db, &self.contents.universe_params),
                ListSexprWrapper::serialise_into_node(db, &self.contents.ty),
            ]
        }
    }
}
