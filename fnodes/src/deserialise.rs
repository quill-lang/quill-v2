//! Provides utilities for converting from S-expressions to Feather nodes.
//! Deserialisation does not require error recovery, since Feather code is typically
//! not handwritten. It suffices to generate a nice error message for the first syntax error in a file.
//! `?` syntax is useful for stopping after the first parse error.

use std::num::ParseIntError;

use crate::{s_expr::*, SexprParseContext, SexprParser};
use fcommon::{Label, LabelType, Report, ReportKind, Source, Span};

/// An error type used when parsing S-expressions into Feather expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub span: Span,
    pub reason: ParseErrorReason,
}

/// The possible reasons we might have a parse error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseErrorReason {
    /// We tried to parse an integer, and this failed.
    ParseIntError {
        /// What was the string that we tried to convert to an int?
        text: String,
        /// Why did it fail?
        err: ParseIntError,
    },
    /// We expected to see an atom, but found a list.
    ExpectedAtom,
    /// We expected to see a list, but found an atom.
    ExpectedList,
    /// We expected a specific keyword at the start of a list S-expression,
    /// but the first entry in the list was another list.
    ExpectedKeywordFoundList { expected: &'static str },
    /// We expected a specific keyword at the start of a list S-expression,
    /// but the list was empty.
    ExpectedKeywordFoundEmpty { expected: &'static str },
    /// We expected some entries in this list, but none were found.
    Empty,
    /// We expected a specific keyword at the start of a list S-expression,
    /// but the first entry in the list did not match the expected keyword.
    WrongKeyword {
        expected: &'static str,
        found: String,
    },
    /// The amount of elements in this list was different to what was expected.
    WrongArity {
        expected_arity: usize,
        found_arity: usize,
    },
    /// An info type was given more than once.
    RepeatedInfo { info_keyword: &'static str },
}

impl ParseError {
    pub(crate) fn into_report(self, source: Source) -> Report {
        let msg = match self.reason {
            ParseErrorReason::ParseIntError { text, err } => {
                format!("couldn't parse '{}' as int: {}", text, err)
            }
            ParseErrorReason::ExpectedAtom => "expected an atom, but found a list".to_string(),
            ParseErrorReason::ExpectedList => "expected a list, but found an atom".to_string(),
            ParseErrorReason::ExpectedKeywordFoundList { expected } => {
                format!("expected keyword '{}', but found a list", expected)
            }
            ParseErrorReason::ExpectedKeywordFoundEmpty { expected } => format!(
                "expected keyword '{}' at the start of this list, but the list was empty",
                expected
            ),
            ParseErrorReason::Empty => "expected elements in this list".to_string(),
            ParseErrorReason::WrongKeyword { expected, found } => format!(
                "expected keyword '{}', but found keyword '{}'",
                expected, found
            ),
            ParseErrorReason::WrongArity {
                expected_arity,
                found_arity,
            } => format!(
                "expected this list to have {} elements, but found {}",
                expected_arity, found_arity
            ),
            ParseErrorReason::RepeatedInfo { info_keyword } => {
                format!("info keyword '{}' occured twice", info_keyword)
            }
        };

        Report::new(ReportKind::Error, source, self.span.start)
            .with_message(msg)
            .with_label(
                Label::new(source, self.span, LabelType::Error)
                    .with_message("error originated here"),
            )
    }
}

/// Trait implemented by types that can be deserialised from S-expressions.
/// Normally you shouldn't implement this trait yourself, and should instead use
/// [`SexprAtomParsable`] or [`SexprListParsable`].
pub trait SexprParsable: Sized {
    fn parse(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        node: SexprNode,
    ) -> Result<Self, ParseError>;
}

/// Provides the ability to deserialise an atomic S-expression (a string)
/// into this type.
/// The type [`AtomParsableWrapper`], parametrised with `Self`, will then automatically implement
/// [`SexprParsable`].
pub trait SexprAtomParsable: Sized {
    fn parse_atom(db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason>;
}

/// See [`SexprAtomParsable`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomParsableWrapper<T>(pub T);
impl<P> SexprParsable for AtomParsableWrapper<P>
where
    P: SexprAtomParsable,
{
    fn parse(
        _ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        SexprNode { span, contents }: SexprNode,
    ) -> Result<Self, ParseError> {
        match contents {
            SexprNodeContents::Atom(text) => P::parse_atom(db, text)
                .map_err(|reason| ParseError { span, reason })
                .map(AtomParsableWrapper),
            SexprNodeContents::List(_) => Err(ParseError {
                span,
                reason: ParseErrorReason::ExpectedAtom,
            }),
        }
    }
}

/// Provides the ability to deserialise a list S-expression into this type.
/// The type [`ListParsableWrapper`], parametrised with `Self`, will then automatically implement
/// [`SexprParsable`].
pub trait SexprListParsable: Sized {
    /// If this is not None, the list S-expression must start with this keyword.
    /// The keyword will be removed from the list before passed into [`Self::parse_list`].
    const KEYWORD: Option<&'static str>;
    /// The provided span is the span of the entire list S-expression, including parentheses and
    /// the initial keyword if present.
    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError>;
}

/// See [`SexprListParsable`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ListParsableWrapper<T>(pub T);
impl<P> SexprParsable for ListParsableWrapper<P>
where
    P: SexprListParsable,
{
    fn parse(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        SexprNode { span, contents }: SexprNode,
    ) -> Result<Self, ParseError> {
        match contents {
            SexprNodeContents::Atom(_) => Err(ParseError {
                span,
                reason: ParseErrorReason::ExpectedList,
            }),
            SexprNodeContents::List(mut list) => {
                if let Some(keyword) = P::KEYWORD {
                    if let Some(elt) = list.first() {
                        match &elt.contents {
                            SexprNodeContents::Atom(found_keyword) => {
                                if keyword == found_keyword {
                                    // Efficiency won't be a problem - we're only popping once, and the lists won't be that large.
                                    list.remove(0);
                                } else {
                                    return Err(ParseError {
                                        span: elt.span.clone(),
                                        reason: ParseErrorReason::WrongKeyword {
                                            expected: keyword,
                                            found: found_keyword.clone(),
                                        },
                                    });
                                }
                            }
                            SexprNodeContents::List(_) => {
                                return Err(ParseError {
                                    span: elt.span.clone(),
                                    reason: ParseErrorReason::ExpectedKeywordFoundList {
                                        expected: keyword,
                                    },
                                });
                            }
                        }
                    } else {
                        return Err(ParseError {
                            span,
                            reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                                expected: keyword,
                            },
                        });
                    }
                };
                P::parse_list(ctx, db, span, list).map(ListParsableWrapper)
            }
        }
    }
}

macro_rules! gen_int_parsable {
    ($t:ty) => {
        impl SexprAtomParsable for $t {
            fn parse_atom(_db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
                text.parse()
                    .map_err(|err| ParseErrorReason::ParseIntError { text, err })
            }
        }
    };
}

gen_int_parsable!(i128);
gen_int_parsable!(u128);
gen_int_parsable!(i64);
gen_int_parsable!(u64);
gen_int_parsable!(i32);
gen_int_parsable!(u32);
gen_int_parsable!(i16);
gen_int_parsable!(u16);
gen_int_parsable!(i8);
gen_int_parsable!(u8);

/// If `args` has length `N`, then return the elements as an array.
/// Otherwise, raise a [`ParseErrorReason::WrongArity`] error.
pub fn force_arity<const N: usize>(
    span: Span,
    args: Vec<SexprNode>,
) -> Result<[SexprNode; N], ParseError> {
    args.try_into()
        .map_err(|args_moved: Vec<SexprNode>| ParseError {
            span,
            reason: ParseErrorReason::WrongArity {
                expected_arity: N,
                found_arity: args_moved.len(),
            },
        })
}
