use fcommon::Span;

use crate::{basic_nodes::Name, expr::*, *};

/// An inductive data type.
pub struct InductiveContents {
    /// The name of this inductive data type inside the current module.
    pub name: Name,
    /// A list of strings representing names of universe parameters.
    pub universe_params: Vec<Name>,
    /// The type of the inductive data type.
    /// If there are no parameters, this will be something like `Sort u`.
    /// If there are type parameters, say `(a: T)`, it will be a function from this `T` to a sort.
    pub ty: Expr,
    /// A list of all of the type constructors associated with this inductive data type.
    pub constructors: Vec<TypeConstructor>,
}

pub struct TypeConstructor {
    /// The unique name of this type constructor.
    pub name: Name,
    /// The type represented by this type constructor.
    /// For instance, a structure `Foo` with one field `foo: T` might have a type constructor with type `(foo: T) -> Foo`.
    pub ty: Expr,
}

pub type Inductive = Node<InductiveContents>;

impl ListSexpr for TypeConstructor {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, ty] = force_arity(span, args)?;
        Ok(Self {
            name: Name::parse(ctx, db, name)?,
            ty: ListSexprWrapper::parse(ctx, db, ty)?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            Name::serialise(&self.name, ctx, db),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.ty),
        ]
    }
}

impl ListSexpr for Inductive {
    const KEYWORD: Option<&'static str> = Some("ind");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, infos, universe_params, ty, constructors] = force_arity(span.clone(), args)?;

        let def = Node::new(
            ctx.node_id_gen.gen(),
            span.clone(),
            InductiveContents {
                name: Name::parse(ctx, db, name)?,
                universe_params: ListSexprWrapper::parse(ctx, db, universe_params)?,
                ty: ListSexprWrapper::parse(ctx, db, ty)?,
                constructors: ListSexprWrapper::parse(ctx, db, constructors)?,
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
                    ctx.process_inductive_info(db, &def, info)?;
                }
            }
        }
        Ok(def)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let infos = SexprNodeContents::List(ctx.process_inductive_info(db, self, ctx));
        vec![
            self.contents.name.serialise(ctx, db),
            SexprNode {
                contents: infos,
                span: 0..0,
            },
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.universe_params),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.ty),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.constructors),
        ]
    }
}
