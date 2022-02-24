use crate::deserialise::SexprParsable;
use crate::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroU64(u64);

impl SexprListParsable for IntroU64 {
    const KEYWORD: Option<&'static str> = Some("iu64");

    fn parse_list(
        infos: &mut NodeInfoInserters,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(AtomParsableWrapper::parse(infos, value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct IntroUnit;

impl SexprListParsable for IntroUnit {
    const KEYWORD: Option<&'static str> = Some("iunit");

    fn parse_list(
        _infos: &mut NodeInfoInserters,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [] = force_arity(span, args)?;
        Ok(Self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprAt(Span);

impl SexprListParsable for ExprAt {
    const KEYWORD: Option<&'static str> = Some("at");

    fn parse_list(
        infos: &mut NodeInfoInserters,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(ListParsableWrapper::parse(infos, value)?.0))
    }
}

macro_rules! gen_variants {
    ($n: ident $label: tt: $( $t: ident )*) => {
        #[derive(Debug, Clone, PartialEq, Eq)]
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

            fn parse_list(infos: &mut NodeInfoInserters, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
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
                        $t::KEYWORD => $t::parse_list(infos, span, args)?.into(),
                    )*
                    _ => {
                        return Err(ParseError {
                            span: args.first().unwrap().span.clone(),
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
    IntroU64
    IntroUnit
}

pub type Expr = Node<ExprContents>;

impl SexprListParsable for Expr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        infos: &mut NodeInfoInserters,
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
                ListParsableWrapper::<ExprContents>::parse(infos, args.remove(0))?.0;
            let expr = Node::new(span, expr_contents);
            for info in args {
                infos.process_expr_info(&expr, info)?;
            }
            Ok(expr)
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(infos, span.clone(), args)
                .map(|expr_contents| Node::new(span, expr_contents))
        }
    }
}
