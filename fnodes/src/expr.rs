use fcommon::Span;

use crate::basic_nodes::{DeBruijnIndex, Name, QualifiedName};
use crate::deserialise::SexprParsable;
use crate::*;

/// Move the value of a local variable into this expression.
/// The value of this variable is a de Bruijn index.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroLocal(pub DeBruijnIndex);

impl SexprListParsable for IntroLocal {
    const KEYWORD: Option<&'static str> = Some("local");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(AtomParsableWrapper::parse(ctx, db, value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroU64(u64);

impl SexprListParsable for IntroU64 {
    const KEYWORD: Option<&'static str> = Some("iu64");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(AtomParsableWrapper::parse(ctx, db, value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroFalse;

impl SexprListParsable for IntroFalse {
    const KEYWORD: Option<&'static str> = Some("ifalse");

    fn parse_list(
        _ctx: &mut SexprParseContext,
        _db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [] = force_arity(span, args)?;
        Ok(Self)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroTrue;

impl SexprListParsable for IntroTrue {
    const KEYWORD: Option<&'static str> = Some("itrue");

    fn parse_list(
        _ctx: &mut SexprParseContext,
        _db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [] = force_arity(span, args)?;
        Ok(Self)
    }
}

macro_rules! gen_nullary {
    ($n:ident $s:expr) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub struct $n;

        impl SexprListParsable for $n {
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
        }
    };
}

gen_nullary!(IntroUnit "iunit");
gen_nullary!(FormU64 "fu64");
gen_nullary!(FormBool "fbool");
gen_nullary!(FormUnit "funit");

// TODO: Check for duplicates in each component-related thing.

#[derive(Debug, PartialEq, Eq)]
pub struct ComponentContents {
    pub name: Name,
    pub ty: Expr,
}

pub type Component = Node<ComponentContents>;

impl SexprListParsable for Component {
    const KEYWORD: Option<&'static str> = Some("comp");

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
        let ty = ListParsableWrapper::<Expr>::parse(ctx, db, args.remove(0))?.0;
        let component = Node::new(ctx.node_id_gen.gen(), span, ComponentContents { name, ty });
        for info in args {
            ctx.process_component_info(db, &component, info)?;
        }
        Ok(component)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IntroComponent {
    name: Name,
    expr: Expr,
}

impl SexprListParsable for IntroComponent {
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
            expr: ListParsableWrapper::parse(ctx, db, expr)?.0,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IntroProduct {
    fields: Vec<IntroComponent>,
}

impl SexprListParsable for IntroProduct {
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
                .map(|arg| ListParsableWrapper::parse(ctx, db, arg).map(|x| x.0))
                .collect::<Result<_, _>>()?,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct FormProduct {
    fields: Vec<Component>,
}

impl SexprListParsable for FormProduct {
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
                .map(|arg| ListParsableWrapper::parse(ctx, db, arg).map(|x| x.0))
                .collect::<Result<_, _>>()?,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecursorProduct {
    func: Box<Expr>,
    expr: Box<Expr>,
}

impl SexprListParsable for RecursorProduct {
    const KEYWORD: Option<&'static str> = Some("rprod");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [func, expr] = force_arity(span, args)?;
        Ok(Self {
            func: Box::new(ListParsableWrapper::parse(ctx, db, func)?.0),
            expr: Box::new(ListParsableWrapper::parse(ctx, db, expr)?.0),
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Inst(pub QualifiedName);

impl SexprListParsable for Inst {
    const KEYWORD: Option<&'static str> = Some("inst");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(ListParsableWrapper::parse(ctx, db, value)?.0))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ExprTy(Expr);

impl SexprListParsable for ExprTy {
    const KEYWORD: Option<&'static str> = Some("ty");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(ListParsableWrapper::<Expr>::parse(ctx, db, value)?.0))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Let<E = Expr> {
    /// The value to assign to the new bound variable.
    pub to_assign: Box<E>,
    /// The main body of the expression to be executed after assigning the value.
    pub body: Box<E>,
}

impl SexprListParsable for Let {
    const KEYWORD: Option<&'static str> = Some("let");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [to_assign, body] = force_arity(span, args)?;
        Ok(Let {
            to_assign: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, to_assign)?.0),
            body: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, body)?.0),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lambda<E = Expr> {
    /// The amount of new variables to be bound in the body of the lambda.
    pub binding_count: u32,
    /// The body of the lambda, also called the lambda term.
    pub body: Box<E>,
}

impl SexprListParsable for Lambda {
    const KEYWORD: Option<&'static str> = Some("lambda");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [binding_count, body] = force_arity(span, args)?;
        Ok(Lambda {
            binding_count: AtomParsableWrapper::<u32>::parse(ctx, db, binding_count)?.0,
            body: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, body)?.0),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Apply<E = Expr> {
    /// The function to be invoked.
    pub function: Box<E>,
    /// The argument to apply to the function.
    pub argument: DeBruijnIndex,
}

impl SexprListParsable for Apply {
    const KEYWORD: Option<&'static str> = Some("ap");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [function, argument] = force_arity(span, args)?;
        Ok(Apply {
            function: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, function)?.0),
            argument: AtomParsableWrapper::<DeBruijnIndex>::parse(ctx, db, argument)?.0,
        })
    }
}

/// An inference variable.
/// May have theoretically any type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

impl SexprListParsable for Var {
    const KEYWORD: Option<&'static str> = Some("var");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [num] = force_arity(span, args)?;
        Ok(Var(AtomParsableWrapper::<u32>::parse(ctx, db, num)?.0))
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
pub struct FormFunc<E = Expr> {
    /// The type of the parameter.
    pub parameter: Box<E>,
    /// The type of the result.
    pub result: Box<E>,
}

impl SexprListParsable for FormFunc {
    const KEYWORD: Option<&'static str> = Some("ffunc");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [parameter, result] = force_arity(span, args)?;
        Ok(FormFunc {
            parameter: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, parameter)?.0),
            result: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, result)?.0),
        })
    }
}

macro_rules! gen_variants {
    ($n: ident $label: tt: $( $t: ident )*) => {
        #[derive(Debug, PartialEq, Eq)]
        pub enum $n {
            $( $t($t) ),*
        }

        impl $n {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    $(
                        Self::$t(_) => $t::KEYWORD.unwrap()
                    ),*
                }
            }
        }

        $(
            impl TryFrom<$n> for $t {
                type Error = &'static str;
                fn try_from(value: $n) -> Result<Self, Self::Error> {
                    if let $n::$t(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
                }
            }

            impl From<$t> for $n {
                fn from(value: $t) -> $n {
                    $n::$t(value)
                }
            }
        )*

        impl SexprListParsable for $n {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
                if args.is_empty() {
                    return Err(ParseError {
                        span,
                        reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                            expected: $label,
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
                            expected: $label,
                        },
                    });
                };

                // Reduce the span to only contain the arguments, not the keyword.
                let span = (first.span.end + 1)..span.end - 1;

                Ok(match Some(keyword) {
                    $(
                        $t::KEYWORD => $t::parse_list(ctx, db, span, args)?.into(),
                    )*
                    _ => {
                        return Err(ParseError {
                            span: first.span.clone(),
                            reason: ParseErrorReason::WrongKeyword {
                                expected: $label,
                                found: keyword.to_string(),
                            },
                        })
                    }
                })
            }
        }
    };
}

gen_variants! {
    ExprContents "<any expression>":

    IntroLocal

    IntroU64
    IntroFalse
    IntroTrue
    IntroUnit

    FormU64
    FormBool
    FormUnit

    IntroProduct
    FormProduct
    RecursorProduct

    Inst
    Let
    Lambda
    Apply
    Var

    FormFunc
}

impl ExprContents {
    pub fn sub_expressions(&self) -> Vec<&Expr> {
        match self {
            ExprContents::Let(Let { to_assign, body }) => vec![&*to_assign, &*body],
            ExprContents::Lambda(Lambda { body, .. }) => vec![&*body],
            ExprContents::Apply(Apply { function, .. }) => vec![&*function],
            ExprContents::FormFunc(FormFunc { parameter, result }) => vec![&*parameter, &*result],
            _ => Vec::new(),
        }
    }

    pub fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
        match self {
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

impl SexprListParsable for Expr {
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
            let expr_contents =
                ListParsableWrapper::<ExprContents>::parse(ctx, db, args.remove(0))?.0;
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
}
