use fcommon::Span;

use crate::basic_nodes::{DeBruijnIndex, QualifiedName};
use crate::deserialise::SexprParsable;
use crate::*;

/// Move the value of a local variable into this expression.
/// The value of this variable is a de Bruijn index.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroLocal(DeBruijnIndex);

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroUnit;

impl SexprListParsable for IntroUnit {
    const KEYWORD: Option<&'static str> = Some("iunit");

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

#[derive(Debug, PartialEq, Eq)]
pub struct Inst(QualifiedName);

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

#[derive(Debug, PartialEq, Eq)]
pub struct Let {
    /// The value to assign to the new bound variable.
    to_assign: Box<Expr>,
    /// The main body of the expression to be executed after assigning the value.
    body: Box<Expr>,
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

#[derive(Debug, PartialEq, Eq)]
pub struct Lambda {
    /// The amount of new variables to be bound in the body of the lambda.
    binding_count: u32,
    /// The body of the lambda, also called the lambda term.
    body: Box<Expr>,
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

#[derive(Debug, PartialEq, Eq)]
pub struct Apply {
    /// The function to be invoked.
    function: Box<Expr>,
    /// The argument to apply to the function.
    argument: Box<Expr>,
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
            argument: Box::new(ListParsableWrapper::<Expr>::parse(ctx, db, argument)?.0),
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
    Inst
    Let
    Lambda
    Apply
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