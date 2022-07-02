use fcommon::{Source, Span};

use crate::{
    basic_nodes::{Name, Provenance},
    expr::*,
    *,
};

/// An inductive data type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct InductiveContents {
    /// The name of this inductive data type inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the inductive data type.
    /// If there are no parameters, this will be something like `Sort u`.
    /// If there are type parameters, say `(a: T)`, it will be a function from this `T` to a sort.
    pub ty: Expr,
    /// Given that `ty` is an n-ary (dependent) function to some [`Sort`], how many of the first parameters
    /// to this function are "global"? All introduction rules must have the same sequence of global parameters,
    /// but may have different sequences of index parameters (the name for non-global parameters).
    /// This number must be at most `n`, if `ty` is an n-ary function. This is guaranteed if this [`Inductive`]
    /// has been certified by the kernel.
    pub global_params: u32,
    /// A list of all of the type constructors associated with this inductive data type.
    pub constructors: Vec<TypeConstructor>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TypeConstructor {
    /// The unique name of this type constructor.
    pub name: Name,
    /// The type represented by this type constructor.
    /// For instance, a structure `Foo` with one field `foo: T` might have a type constructor with type `(foo: T) -> Foo`.
    pub ty: Expr,
}

#[derive(PartialEq, Eq, Hash)]
pub struct Inductive {
    /// The origin of the expression.
    pub provenance: Provenance,
    /// The actual contents of this expression.
    pub contents: InductiveContents,
}

impl std::fmt::Debug for Inductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.provenance, self.contents)
    }
}

impl ListSexpr for TypeConstructor {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, ty] = force_arity(span, args)?;
        Ok(Self {
            name: Name::parse(db, source, name)?,
            ty: ListSexprWrapper::parse(db, source, ty)?,
        })
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            Name::serialise(&self.name, db),
            ListSexprWrapper::serialise_into_node(db, &self.ty),
        ]
    }
}

impl ListSexpr for Inductive {
    const KEYWORD: Option<&'static str> = Some("ind");

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, infos, universe_params, ty, global_params, constructors] =
            force_arity(span.clone(), args)?;

        let inductive = Inductive {
            provenance: Provenance::Sexpr {
                source,
                span: span.clone(),
            },
            contents: InductiveContents {
                name: Name::parse(db, source, name)?,
                universe_params: ListSexprWrapper::parse(db, source, universe_params)?,
                ty: ListSexprWrapper::parse(db, source, ty)?,
                global_params: AtomicSexprWrapper::parse(db, source, global_params)?,
                constructors: ListSexprWrapper::parse(db, source, constructors)?,
            },
        };
        // TODO: node infos
        // match infos.contents {
        //     SexprNodeContents::Atom(_) => {
        //         return Err(ParseError {
        //             span,
        //             reason: ParseErrorReason::ExpectedList,
        //         })
        //     }
        //     SexprNodeContents::List(infos) => {
        //         for info in infos {
        //             ctx.process_inductive_info(db, &inductive, info)?;
        //         }
        //     }
        // }
        Ok(inductive)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        //let infos = SexprNodeContents::List(ctx.process_inductive_info(db, self, ctx));
        vec![
            self.contents.name.serialise(db),
            // SexprNode {
            //     contents: infos,
            //     span: 0..0,
            // },
            ListSexprWrapper::serialise_into_node(db, &self.contents.universe_params),
            ListSexprWrapper::serialise_into_node(db, &self.contents.ty),
            ListSexprWrapper::serialise_into_node(db, &self.contents.constructors),
        ]
    }
}
