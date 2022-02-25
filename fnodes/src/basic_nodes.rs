use fcommon::Span;
use lasso::Spur;

use crate::*;

impl SexprListParsable for Span {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        infos: &mut NodeInfoInserters,
        interner: &StringInterner,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [start, end] = force_arity(span, args)?;

        // For the sake of compatibility across platforms, we enforce that spans are decoded as `u32`s first.

        let start = AtomParsableWrapper::<u32>::parse(infos, interner, start)?.0;
        let end = AtomParsableWrapper::<u32>::parse(infos, interner, end)?.0;

        Ok((start as usize)..(end as usize))
    }
}

impl SexprAtomParsable for Spur {
    fn parse_atom(interner: &StringInterner, text: String) -> Result<Self, ParseErrorReason> {
        Ok(interner.get_or_intern(text))
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
pub type Name = Node<Spur>;

impl SexprParsable for Name {
    fn parse(
        infos: &mut NodeInfoInserters,
        interner: &StringInterner,
        node: SexprNode,
    ) -> Result<Self, ParseError> {
        match node.contents {
            SexprNodeContents::Atom(text) => Ok(Node::new(node.span, interner.get_or_intern(text))),
            SexprNodeContents::List(entries) => {
                let name = if let Some(first) = entries.first() {
                    match &first.contents {
                        SexprNodeContents::Atom(text) => {
                            Node::new(node.span, interner.get_or_intern(text))
                        }
                        SexprNodeContents::List(_) => {
                            return Err(ParseError {
                                span: node.span.clone(),
                                reason: ParseErrorReason::ExpectedKeywordFoundList {
                                    expected: "<any name>",
                                },
                            })
                        }
                    }
                } else {
                    return Err(ParseError {
                        span: node.span.clone(),
                        reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                            expected: "<any name>",
                        },
                    });
                };

                for info in entries.into_iter().skip(1) {
                    infos.process_name_info(interner, &name, info)?;
                }

                Ok(name)
            }
        }
    }
}

/// A qualified name that may have been written in code, rather than one simply stored internally
/// that was never written in code (see [`fcommon::Path`] for that use case).
#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedName(pub Vec<Name>);

impl SexprListParsable for QualifiedName {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        infos: &mut NodeInfoInserters,
        interner: &StringInterner,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| Name::parse(infos, interner, arg))
            .collect::<Result<Vec<_>, _>>()
            .map(QualifiedName)
    }
}

/// Specifies where in source (Quill) code a node came from.
/// This is often used in names and expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSpan(Span);

impl SexprListParsable for SourceSpan {
    const KEYWORD: Option<&'static str> = Some("at");

    fn parse_list(
        infos: &mut NodeInfoInserters,
        interner: &StringInterner,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(ListParsableWrapper::parse(infos, interner, value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnIndex(u32);

impl SexprAtomParsable for DeBruijnIndex {
    fn parse_atom(interner: &StringInterner, text: String) -> Result<Self, ParseErrorReason> {
        u32::parse_atom(interner, text).map(Self)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use chumsky::Parser;
    use lasso::ThreadedRodeo;

    use super::*;

    #[test]
    fn span() {
        let pairs = [
            ("(123 324)", Ok(123..324)),
            ("(0 0)", Ok(0..0)),
            (
                "(3 -45)",
                Err(ParseError {
                    span: 3..6,
                    reason: ParseErrorReason::ParseIntError {
                        text: "-45".to_string(),
                        err: "-1".parse::<u32>().unwrap_err(),
                    },
                }),
            ),
            (
                "(3 (2))",
                Err(ParseError {
                    span: 3..6,
                    reason: ParseErrorReason::ExpectedAtom,
                }),
            ),
        ];

        let interner = Arc::new(ThreadedRodeo::new());
        for (string, expected) in pairs {
            let actual = ListParsableWrapper::<Span>::parse(
                &mut NodeInfoInserters::default(),
                &interner,
                sexpr_parser().parse(string).unwrap(),
            )
            .map(|x| x.0);
            assert_eq!(actual, expected);
        }
    }
}
