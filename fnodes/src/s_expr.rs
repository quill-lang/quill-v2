//! Feather nodes can be serialised into S-expressions.
//! This module provides functionality for both serialisation and deserialisation.

use chumsky::prelude::*;
use fcommon::{Dr, Span};

use crate::{ParseError, ParseErrorReason};

/// Represents a node in a tree of S-expressions.
/// All values are stored as strings, and have no semantic meaning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SexprNode {
    pub contents: SexprNodeContents,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SexprNodeContents {
    Atom(String),
    List(Vec<SexprNode>),
}

/// Parses an S-expression.
pub fn parse_sexpr(source: &str) -> Dr<SexprNode> {
    match sexpr_parser().parse(source) {
        Ok(result) => result.into(),
        Err(_) => todo!(),
    }
}

/// Parses an S-expression.
fn sexpr_parser() -> impl Parser<char, SexprNode, Error = Simple<char>> {
    // Adapted from the JSON example <https://github.com/zesterer/chumsky/blob/master/examples/json.rs>.
    let expr = recursive(|sexpr| {
        let escape = just('\\').ignore_then(
            just('\\')
                .or(just('/'))
                .or(just('"'))
                .or(just('b').to('\x08'))
                .or(just('f').to('\x0C'))
                .or(just('n').to('\n'))
                .or(just('r').to('\r'))
                .or(just('t').to('\t')),
        );

        let string = just('"')
            .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .map(SexprNodeContents::Atom)
            .labelled("string");

        let other_atom = filter::<_, _, Simple<char>>(|c: &char| {
            !c.is_whitespace() && !matches!(c, '(' | ')' | '"')
        })
        .repeated()
        .at_least(1)
        .map(|chars| SexprNodeContents::Atom(chars.into_iter().collect()))
        .labelled("other_atom");

        let atom = string.or(other_atom);

        let list = sexpr
            .padded()
            .repeated()
            .map(SexprNodeContents::List)
            .delimited_by(just('('), just(')'))
            .labelled("list");

        list.or(atom)
            .map_with_span(|contents, span| SexprNode { contents, span })
    });
    expr.padded().then_ignore(end())
}

/// Suppose that this node is of the form `(kwd ...)`.
/// Then return `kwd`, or a parse error if this was not the case.
pub fn find_keyword_from_list(node: &SexprNode) -> Result<String, ParseError> {
    match &node.contents {
        SexprNodeContents::Atom(_) => Err(ParseError {
            span: node.span.clone(),
            reason: ParseErrorReason::ExpectedList,
        }),
        SexprNodeContents::List(entries) => {
            if let Some(first) = entries.first() {
                match &first.contents {
                    SexprNodeContents::Atom(kwd) => Ok(kwd.clone()),
                    SexprNodeContents::List(_) => Err(ParseError {
                        span: node.span.clone(),
                        reason: ParseErrorReason::ExpectedKeywordFoundList {
                            expected: "<any expression info>",
                        },
                    }),
                }
            } else {
                Err(ParseError {
                    span: node.span.clone(),
                    reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                        expected: "<any expression info>",
                    },
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::s_expr::*;

    #[test]
    fn atom() {
        let value = sexpr_parser().parse("123").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::Atom("123".to_string()),
            span: 0..3,
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn list() {
        let value = sexpr_parser().parse("(a b c)").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("a".to_string()),
                    span: 1..2,
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("b".to_string()),
                    span: 3..4,
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("c".to_string()),
                    span: 5..6,
                },
            ]),
            span: 0..7,
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn string() {
        let value = sexpr_parser()
            .parse(r#"("Hello, world!" "escaping\\\"")"#)
            .unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("Hello, world!".to_string()),
                    span: 1..16,
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("escaping\\\"".to_string()),
                    span: 17..31,
                },
            ]),
            span: 0..32,
        };
        assert_eq!(value, expected);
    }

    #[test]
    fn hierarchy() {
        let value = sexpr_parser().parse("(a b (c d) ((e) f))").unwrap();
        let expected = SexprNode {
            contents: SexprNodeContents::List(vec![
                SexprNode {
                    contents: SexprNodeContents::Atom("a".to_string()),
                    span: 1..2,
                },
                SexprNode {
                    contents: SexprNodeContents::Atom("b".to_string()),
                    span: 3..4,
                },
                SexprNode {
                    contents: SexprNodeContents::List(vec![
                        SexprNode {
                            contents: SexprNodeContents::Atom("c".to_string()),
                            span: 6..7,
                        },
                        SexprNode {
                            contents: SexprNodeContents::Atom("d".to_string()),
                            span: 8..9,
                        },
                    ]),
                    span: 5..10,
                },
                SexprNode {
                    contents: SexprNodeContents::List(vec![
                        SexprNode {
                            contents: SexprNodeContents::List(vec![SexprNode {
                                contents: SexprNodeContents::Atom("e".to_string()),
                                span: 13..14,
                            }]),
                            span: 12..15,
                        },
                        SexprNode {
                            contents: SexprNodeContents::Atom("f".to_string()),
                            span: 16..17,
                        },
                    ]),
                    span: 11..18,
                },
            ]),
            span: 0..19,
        };
        assert_eq!(value, expected);
    }
}
