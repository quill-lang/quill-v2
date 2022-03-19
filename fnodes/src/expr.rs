use fcommon::{Span, Str};

use crate::basic_nodes::{DeBruijnIndex, Name, QualifiedName};
use crate::serialise::SexprParsable;
use crate::*;

// TODO: Clean up this whole file, there's lots of boilerplate.

macro_rules! gen_nullary {
    (($($start:tt)*) $n:ident $s:expr) => {
        $($start)*
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub struct $n;

        impl ListSexpr for $n {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                _ctx: &mut SexprParseContext,
                _db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [] = force_arity(span, args)?;
                Ok(Self)
            }

            fn serialise(
                &self,
                _ctx: &SexprSerialiseContext,
                _db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                Vec::new()
            }
        }
    };
    ($n:ident $s:expr) => {
        gen_nullary!(() $n $s);
    }
}

macro_rules! gen_unary {
    (($($start:tt)*) $n:ident($i:ident $t:ty) $s:expr) => {
        $($start)*
        #[derive(Debug, PartialEq, Eq)]
        pub struct $n(pub $t);

        impl ListSexpr for $n {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                ctx: &mut SexprParseContext,
                db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [value] = force_arity(span, args)?;
                Ok(Self($i::parse(ctx, db, value)?))
            }

            fn serialise(
                &self,
                ctx: &SexprSerialiseContext,
                db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                vec![$i::serialise_into_node(ctx, db, &self.0)]
            }
        }
    };
    ($n:ident($i:ident $t:ty) $s:expr) => {
        gen_unary!(() $n($i $t) $s);
    }
}

gen_unary! {
    (
        /// Move the value of a local variable into this expression.
        /// The value of this variable is a de Bruijn index.
        #[derive(Copy, Clone)]
    )
    IntroLocal(AtomicSexprWrapper DeBruijnIndex) "local"
}

gen_unary! {
    (
        #[derive(Copy, Clone)]
    )
    IntroU64(AtomicSexprWrapper u64) "iu64"
}

gen_nullary!(IntroFalse "ifalse");
gen_nullary!(IntroTrue "itrue");

gen_nullary!(IntroUnit "iunit");
gen_nullary!(FormU64 "fu64");
gen_nullary!(FormBool "fbool");
gen_nullary!(FormUnit "funit");

// TODO: Check for duplicates in each component-related thing.

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ComponentContents<N, E> {
    pub name: N,
    pub ty: E,
}

pub type Component<N, E> = Node<ComponentContents<N, E>>;

impl ListSexpr for Component<Name, Expr> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.len() < 2 {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::WrongArity {
                    expected_arity: 2,
                    found_arity: args.len(),
                },
            });
        }
        let name = Name::parse(ctx, db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(ctx, db, args.remove(0))?;
        let component = Node::new(ctx.node_id_gen.gen(), span, ComponentContents { name, ty });
        for info in args {
            ctx.process_component_info(db, &component, info)?;
        }
        Ok(component)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: component info
        vec![
            self.contents.name.serialise(ctx, db),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.ty),
        ]
    }
}

impl<E> ListSexpr for ComponentContents<Str, E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.len() < 2 {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::WrongArity {
                    expected_arity: 2,
                    found_arity: args.len(),
                },
            });
        }
        let name = AtomicSexprWrapper::parse(ctx, db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(ctx, db, args.remove(0))?;
        Ok(ComponentContents { name, ty })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(ctx, db, &self.name),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.ty),
        ]
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntroComponent<N, E> {
    pub name: N,
    pub expr: E,
}

impl ListSexpr for IntroComponent<Name, Expr> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [name, expr] = force_arity(span, args)?;
        Ok(Self {
            name: Name::parse(ctx, db, name)?,
            expr: ListSexprWrapper::parse(ctx, db, expr)?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(ctx, db, &self.name.contents),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.expr),
        ]
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntroProduct<N, E> {
    pub fields: Vec<IntroComponent<N, E>>,
}

impl ListSexpr for IntroProduct<Name, Expr> {
    const KEYWORD: Option<&'static str> = Some("iprod");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        Ok(Self {
            fields: args
                .into_iter()
                .map(|arg| ListSexprWrapper::parse(ctx, db, arg))
                .collect::<Result<_, _>>()?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.fields
            .iter()
            .map(|value| ListSexprWrapper::serialise_into_node(ctx, db, value))
            .collect()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FormProduct<C> {
    pub fields: Vec<C>,
}

impl ListSexpr for FormProduct<Component<Name, Expr>> {
    const KEYWORD: Option<&'static str> = Some("fprod");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        Ok(Self {
            fields: args
                .into_iter()
                .map(|arg| ListSexprWrapper::parse(ctx, db, arg))
                .collect::<Result<_, _>>()?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.fields
            .iter()
            .map(|value| ListSexprWrapper::serialise_into_node(ctx, db, value))
            .collect()
    }
}

impl<E> ListSexpr for FormProduct<ComponentContents<Str, E>>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = Some("fprod");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        Ok(Self {
            fields: args
                .into_iter()
                .map(|arg| ListSexprWrapper::parse(ctx, db, arg))
                .collect::<Result<_, _>>()?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.fields
            .iter()
            .map(|value| ListSexprWrapper::serialise_into_node(ctx, db, value))
            .collect()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MatchProduct<N, E> {
    pub fields: Vec<N>,
    pub product: Box<E>,
    pub body: Box<E>,
}

impl ListSexpr for MatchProduct<Name, Expr> {
    const KEYWORD: Option<&'static str> = Some("mprod");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [fields, product, body] = force_arity(span, args)?;
        Ok(Self {
            fields: ListSexprWrapper::parse(ctx, db, fields)?,
            product: Box::new(ListSexprWrapper::parse(ctx, db, product)?),
            body: Box::new(ListSexprWrapper::parse(ctx, db, body)?),
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            ListSexprWrapper::serialise_into_node(ctx, db, &self.fields),
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.product),
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.body),
        ]
    }
}

gen_unary!(Inst(ListSexprWrapper QualifiedName) "inst");
gen_unary!(ExprTy(ListSexprWrapper Expr) "ty");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Let<E> {
    /// The value to assign to the new bound variable.
    pub to_assign: Box<E>,
    /// The main body of the expression to be executed after assigning the value.
    pub body: Box<E>,
}

impl<E> ListSexpr for Let<E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = Some("let");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [to_assign, body] = force_arity(span, args)?;
        Ok(Let {
            to_assign: Box::new(ListSexprWrapper::parse(ctx, db, to_assign)?),
            body: Box::new(ListSexprWrapper::parse(ctx, db, body)?),
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.to_assign),
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.body),
        ]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lambda<E> {
    /// The amount of new variables to be bound in the body of the lambda.
    pub binding_count: u32,
    /// The body of the lambda, also called the lambda term.
    pub body: Box<E>,
}

impl<E> ListSexpr for Lambda<E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = Some("lambda");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [binding_count, body] = force_arity(span, args)?;
        Ok(Lambda {
            binding_count: AtomicSexprWrapper::<u32>::parse(ctx, db, binding_count)?,
            body: Box::new(ListSexprWrapper::parse(ctx, db, body)?),
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(ctx, db, &self.binding_count),
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.body),
        ]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Apply<E> {
    /// The function to be invoked.
    pub function: Box<E>,
    /// The argument to apply to the function.
    pub argument: DeBruijnIndex,
}

impl<E> ListSexpr for Apply<E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = Some("ap");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [function, argument] = force_arity(span, args)?;
        Ok(Apply {
            function: Box::new(ListSexprWrapper::parse(ctx, db, function)?),
            argument: AtomicSexprWrapper::parse(ctx, db, argument)?,
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.function),
            AtomicSexprWrapper::serialise_into_node(ctx, db, &self.argument),
        ]
    }
}

/// An inference variable.
/// May have theoretically any type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

impl ListSexpr for Var {
    const KEYWORD: Option<&'static str> = Some("var");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [num] = force_arity(span, args)?;
        AtomicSexprWrapper::<u32>::parse(ctx, db, num).map(Self)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![AtomicSexprWrapper::serialise_into_node(ctx, db, &self.0)]
    }
}

/// Generates unique inference variable names.
pub struct VarGenerator {
    next_var: Var,
}

impl Default for VarGenerator {
    fn default() -> Self {
        Self { next_var: Var(0) }
    }
}

impl VarGenerator {
    pub fn gen(&mut self) -> Var {
        let result = self.next_var;
        self.next_var.0 += 1;
        result
    }
}

// TODO: Document this in the spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormFunc<E> {
    /// The type of the parameter.
    pub parameter: Box<E>,
    /// The type of the result.
    pub result: Box<E>,
}

impl<E> ListSexpr for FormFunc<E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = Some("ffunc");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [parameter, result] = force_arity(span, args)?;
        Ok(FormFunc {
            parameter: Box::new(ListSexprWrapper::parse(ctx, db, parameter)?),
            result: Box::new(ListSexprWrapper::parse(ctx, db, result)?),
        })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.parameter),
            ListSexprWrapper::serialise_into_node(ctx, db, &*self.result),
        ]
    }
}

gen_nullary!(FormUniverse "funiverse");

macro_rules! gen_variants {
    ($( $name: ident: $type: ty, $path: path );*) => {
        /// # Adding variants
        /// When adding a new variant to [`ExprContents`], make sure to update:
        /// - [`ExprContents::sub_expressions`]
        /// - [`ExprContents::sub_expressions_mut`]
        #[derive(Debug, PartialEq, Eq)]
        pub enum ExprContents {
            $( $name($type) ),*
        }

        impl ExprContents {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    $(
                        Self::$name(_) => <$path>::KEYWORD.unwrap()
                    ),*
                }
            }
        }

        $(
            impl TryFrom<ExprContents> for $type {
                type Error = &'static str;
                fn try_from(value: ExprContents) -> Result<Self, Self::Error> {
                    if let ExprContents::$name(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
                }
            }

            impl From<$type> for ExprContents {
                fn from(value: $type) -> ExprContents {
                    ExprContents::$name(value)
                }
            }
        )*

        impl ListSexpr for ExprContents {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
                if args.is_empty() {
                    return Err(ParseError {
                        span,
                        reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                            expected: "<any expression>",
                        },
                    });
                }

                let first = args.remove(0);
                let keyword = if let SexprNodeContents::Atom(value) = &first.contents {
                    value.as_str()
                } else {
                    return Err(ParseError {
                        span: first.span.clone(),
                        reason: ParseErrorReason::ExpectedKeywordFoundList {
                            expected: "<any expression>",
                        },
                    });
                };

                // Reduce the span to only contain the arguments, not the keyword.
                let span = (first.span.end + 1)..span.end - 1;

                Ok(match Some(keyword) {
                    $(
                        <$path>::KEYWORD => <$path>::parse_list(ctx, db, span, args)?.into(),
                    )*
                    _ => {
                        return Err(ParseError {
                            span: first.span.clone(),
                            reason: ParseErrorReason::WrongKeyword {
                                expected: "<any expression>",
                                found: keyword.to_string(),
                            },
                        })
                    }
                })
            }

            fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
                // TODO: expr infos
                match self {
                    $(
                        Self::$name(val) => {
                            let mut result = val.serialise(ctx, db);
                            result.insert(0, SexprNode {
                                contents: SexprNodeContents::Atom(<$path>::KEYWORD.unwrap().to_string()),
                                span: 0..0
                            });
                            result
                        }
                    ),*
                }
            }
        }
    };
}

gen_variants! {
    IntroLocal: IntroLocal, IntroLocal;

    IntroU64: IntroU64, IntroU64;
    IntroFalse: IntroFalse, IntroFalse;
    IntroTrue: IntroTrue, IntroTrue;
    IntroUnit: IntroUnit, IntroUnit;

    FormU64: FormU64, FormU64;
    FormBool: FormBool, FormBool;
    FormUnit: FormUnit, FormUnit;

    IntroProduct: IntroProduct<Name, Expr>, IntroProduct::<Name, Expr>;
    FormProduct: FormProduct<Component<Name, Expr>>, FormProduct::<Component<Name, Expr>>;
    MatchProduct: MatchProduct<Name, Expr>, MatchProduct::<Name, Expr>;

    Inst: Inst, Inst;
    Let: Let<Expr>, Let::<Expr>;
    Lambda: Lambda<Expr>, Lambda::<Expr>;
    Apply: Apply<Expr>, Apply::<Expr>;
    Var: Var, Var;

    FormFunc: FormFunc<Expr>, FormFunc::<Expr>;

    FormUniverse: FormUniverse, FormUniverse
}

impl ExprContents {
    pub fn sub_expressions(&self) -> Vec<&Expr> {
        match self {
            ExprContents::IntroProduct(IntroProduct { fields }) => {
                fields.iter().map(|comp| &comp.expr).collect()
            }
            ExprContents::FormProduct(FormProduct { fields }) => {
                fields.iter().map(|comp| &comp.contents.ty).collect()
            }
            ExprContents::MatchProduct(MatchProduct { product, body, .. }) => {
                vec![product, body]
            }
            ExprContents::Let(Let { to_assign, body }) => vec![&*to_assign, &*body],
            ExprContents::Lambda(Lambda { body, .. }) => vec![&*body],
            ExprContents::Apply(Apply { function, .. }) => vec![&*function],
            ExprContents::FormFunc(FormFunc { parameter, result }) => vec![&*parameter, &*result],
            _ => Vec::new(),
        }
    }

    pub fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
        match self {
            ExprContents::IntroProduct(IntroProduct { fields }) => {
                fields.iter_mut().map(|comp| &mut comp.expr).collect()
            }
            ExprContents::FormProduct(FormProduct { fields }) => fields
                .iter_mut()
                .map(|comp| &mut comp.contents.ty)
                .collect(),
            ExprContents::MatchProduct(MatchProduct { product, body, .. }) => {
                vec![product, body]
            }
            ExprContents::Let(Let { to_assign, body }) => vec![&mut *to_assign, &mut *body],
            ExprContents::Lambda(Lambda { body, .. }) => vec![&mut *body],
            ExprContents::Apply(Apply { function, .. }) => vec![&mut *function],
            ExprContents::FormFunc(FormFunc { parameter, result }) => {
                vec![&mut *parameter, &mut *result]
            }
            _ => Vec::new(),
        }
    }
}

pub type Expr = Node<ExprContents>;

impl ListSexpr for Expr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        // If the first arg is `expr`, this is of the form `expr ExprContents ExprInfo*`.
        let expr_check = args.first().map(|node| {
            if let SexprNodeContents::Atom(string) = &node.contents {
                string == "expr"
            } else {
                false
            }
        });
        if let Some(true) = expr_check {
            // This is of the form `expr ExprContents ExprInfo*`.
            if args.len() < 2 {
                return Err(ParseError {
                    span,
                    reason: ParseErrorReason::WrongArity {
                        expected_arity: 2,
                        found_arity: 1,
                    },
                });
            }
            let _expr_keyword = args.remove(0);
            let expr_contents = ListSexprWrapper::<ExprContents>::parse(ctx, db, args.remove(0))?;
            let expr = Node::new(ctx.node_id_gen.gen(), span, expr_contents);
            for info in args {
                ctx.process_expr_info(db, &expr, info)?;
            }
            Ok(expr)
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(ctx, db, span.clone(), args)
                .map(|expr_contents| Node::new(ctx.node_id_gen.gen(), span, expr_contents))
        }
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let mut infos = ctx.process_expr_info(db, self, ctx);
        if infos.is_empty() {
            self.contents.serialise(ctx, db)
        } else {
            infos.insert(
                0,
                ListSexprWrapper::serialise_into_node(ctx, db, &self.contents),
            );
            infos.insert(
                0,
                AtomicSexprWrapper::serialise_into_node(ctx, db, &"expr".to_string()),
            );
            infos
        }
    }
}
