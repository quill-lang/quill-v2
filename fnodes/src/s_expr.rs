//! Feather nodes can be serialised into S-expressions.
//! This module provides functionality for both serialisation and deserialisation.

use std::collections::HashSet;

use chumsky::prelude::*;
use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, Span};

use crate::{ParseError, ParseErrorReason};

/// Represents a node in a tree of S-expressions.
/// All values are stored as strings, and have no semantic meaning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SexprNode {
    pub contents: SexprNodeContents,
    /// TODO: Only have the span in certain S-expression nodes, using type state.
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SexprNodeContents {
    Atom(String),
    List(Vec<SexprNode>),
}

/// Parses an S-expression.
/// Normally, you should use the query [`crate::SexprParser::parse_sexpr`] instead of calling this function directly.
pub(crate) fn parse_sexpr_from_string(source: Source, source_contents: &str) -> Dr<SexprNode> {
    match sexpr_parser().parse(source_contents) {
        Ok(value) => value.into(),
        Err(errs) => {
            let mut reports = Vec::new();
            for e in errs.into_iter() {
                let msg = format!(
                    "{}{}, expected {}",
                    if e.found().is_some() {
                        "unexpected token"
                    } else {
                        "unexpected end of input"
                    },
                    if let Some(label) = e.label() {
                        format!(" while parsing {}", label)
                    } else {
                        String::new()
                    },
                    if e.expected().len() == 0 {
                        "something else".to_string()
                    } else {
                        e.expected()
                            .map(|expected| match expected {
                                Some(expected) => expected.to_string(),
                                None => "end of input".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    },
                );

                let report = Report::new(ReportKind::Error, source, e.span().start)
                    .with_message(msg)
                    .with_label(Label::new(source, e.span(), LabelType::Error).with_message(
                        format!(
                                "unexpected {}",
                                e.found()
                                    .map(|c| format!("token {}", c))
                                    .unwrap_or_else(|| "end of input".to_string())
                            ),
                    ));

                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                        .with_label(
                            Label::new(source, span.clone(), LabelType::Error)
                                .with_message(format!("unclosed delimiter {}", delimiter)),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report,
                    chumsky::error::SimpleReason::Custom(msg) => report.with_label(
                        Label::new(source, e.span(), LabelType::Error).with_message(msg),
                    ),
                };

                reports.push(report);
            }
            Dr::fail_many(reports)
        }
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

pub struct PrettyPrintSettings {
    /// A list of keywords at the start of list S-expressions.
    /// If such an S-expression begins with this keyword, it will receive no indent.
    pub no_indent_for: HashSet<String>,
}

impl SexprNode {
    /// Converts this in-memory S-expression representation into a string.
    /// This is not the [`std::fmt::Display`] trait; we need to pass additional parameters to control
    /// pretty-printing, for instance.
    pub fn fmt(
        &self,
        f: &mut (dyn std::fmt::Write),
        pretty_print: &PrettyPrintSettings,
        indent_levels: usize,
    ) -> Result<(), std::fmt::Error> {
        fn indent(
            f: &mut (dyn std::fmt::Write),
            indent_levels: usize,
        ) -> Result<(), std::fmt::Error> {
            for _ in 0..(4 * indent_levels) {
                write!(f, " ")?;
            }
            Ok(())
        }

        match &self.contents {
            SexprNodeContents::Atom(atom) => {
                // Unambiguously write this atom as a string.
                if atom.chars().all(|ch| !ch.is_whitespace() && ch != '"') {
                    write!(f, "{}", atom)
                } else {
                    // Escape any problematic characters.
                    write!(f, "{:?}", atom)
                }
            }
            SexprNodeContents::List(elements) => {
                // Depending on pretty-printing settings, we should consider indentation.
                write!(f, "(")?;
                if let Some((first, elts)) = elements.split_first() {
                    if let SexprNodeContents::Atom(first_atom) = &first.contents {
                        if pretty_print.no_indent_for.contains(first_atom) {
                            // Indent no elements.
                            first.fmt(f, pretty_print, indent_levels + 1)?;
                            for elt in elts {
                                write!(f, " ")?;
                                elt.fmt(f, pretty_print, indent_levels + 1)?;
                            }
                        } else {
                            // Indent all but the first element.
                            first.fmt(f, pretty_print, indent_levels + 1)?;
                            for elt in elts {
                                writeln!(f)?;
                                indent(f, indent_levels + 1)?;
                                elt.fmt(f, pretty_print, indent_levels + 1)?;
                            }
                            writeln!(f)?;
                            indent(f, indent_levels)?;
                        }
                    } else {
                        // Indent all elements.
                        writeln!(f)?;
                        indent(f, indent_levels + 1)?;
                        first.fmt(f, pretty_print, indent_levels + 1)?;
                        for elt in elts {
                            writeln!(f)?;
                            indent(f, indent_levels + 1)?;
                            elt.fmt(f, pretty_print, indent_levels + 1)?;
                        }
                        writeln!(f)?;
                        indent(f, indent_levels)?;
                    }
                }
                write!(f, ")")
            }
        }
    }

    /// Uses [`Self::fmt`] to convert this node to a [`String`].
    pub fn to_string(&self, pretty_print: &PrettyPrintSettings) -> String {
        let mut s = String::new();
        self.fmt(&mut s, pretty_print, 0).expect("formatting error");
        s
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
