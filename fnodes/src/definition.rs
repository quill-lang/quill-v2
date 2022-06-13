use fcommon::Span;

use crate::{
    basic_nodes::{Name, Provenance},
    expr::Expr,
    *,
};

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct DefinitionContents {
    /// The name of this definition inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    pub expr: Expr,
}

#[derive(PartialEq, Eq, Hash)]
pub struct Definition {
    /// The origin of the expression.
    provenance: Provenance,
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
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, /* infos, */ universe_params, expr] = force_arity(span.clone(), args)?;

        let def = Definition {
            provenance: Provenance::Sexpr { span: span.clone() },
            contents: DefinitionContents {
                name: Name::parse(db, name)?,
                universe_params: ListSexprWrapper::parse(db, universe_params)?,
                expr: ListSexprWrapper::parse(db, expr)?,
            },
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
        vec![
            self.contents.name.serialise(db),
            // SexprNode {
            //     contents: infos,
            //     span: 0..0,
            // },
            ListSexprWrapper::serialise_into_node(db, &self.contents.universe_params),
            ListSexprWrapper::serialise_into_node(db, &self.contents.expr),
        ]
    }
}
