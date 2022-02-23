use crate::deserialise::SexprParsable;
use crate::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroU64(u64);

impl SexprListParsable for IntroU64 {
    const KEYWORD: Option<&'static str> = Some("iu64");

    fn parse_list(span: Span, args: Vec<SexprNode>) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(AtomParsableWrapper::parse(value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroUnit;

impl SexprListParsable for IntroUnit {
    const KEYWORD: Option<&'static str> = Some("iunit");

    fn parse_list(span: Span, args: Vec<SexprNode>) -> Result<Self, ParseError> {
        let [] = force_arity(span, args)?;
        Ok(Self)
    }
}

macro_rules! gen_expr_contents {
    ($( $t: ident )*) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub enum ExprContents {
            $( $t($t) ),*
        }

        impl ExprContents {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    $(
                        Self::$t(_) => $t::KEYWORD.unwrap()
                    ),*
                }
            }

            fn parse_list_variants(span: Span, keyword: &str, args: Vec<SexprNode>) -> Result<Self, ParseError> {
                Ok(match Some(keyword) {
                    $(
                        $t::KEYWORD => $t::parse_list(span, args)?.into(),
                    )*
                    _ => {
                        return Err(ParseError {
                            span: args.first().unwrap().span.clone(),
                            reason: ParseErrorReason::WrongKeyword {
                                expected: "<any expression>",
                                found: keyword.to_string(),
                            },
                        })
                    }
                })
            }
        }

        $(
            impl TryFrom<ExprContents> for $t {
                type Error = &'static str;
                fn try_from(value: ExprContents) -> Result<Self, Self::Error> {
                    if let ExprContents::$t(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
                }
            }

            impl From<$t> for ExprContents {
                fn from(value: $t) -> ExprContents {
                    ExprContents::$t(value)
                }
            }
        )*
    };
}

gen_expr_contents! {
    IntroU64
    IntroUnit
}

impl SexprListParsable for ExprContents {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
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

        ExprContents::parse_list_variants(span, keyword, args)
    }
}

pub type Expr = Node<ExprContents>;

impl SexprListParsable for Expr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
        // If the first arg is `expr`, this is of the form `expr ExprContents ExprInfo*`.
        let expr_check = args.first().map(|node| {
            if let SexprNodeContents::Atom(string) = &node.contents {
                string == "expr"
            } else {
                false
            }
        });
        if let Some(true) = expr_check {
            // This is of the form `expr ExprContents ExprInfo*`
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
            let expr_contents = ListParsableWrapper::<ExprContents>::parse(args.remove(0))?.0;
            //let info = args.into_iter()
            Ok(Node::new(span, expr_contents))
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(span.clone(), args)
                .map(|expr_contents| Node::new(span, expr_contents))
        }
    }
}
