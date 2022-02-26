use fcommon::{Span, Str};

use crate::*;

impl SexprListParsable for Span {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [start, end] = force_arity(span, args)?;

        // For the sake of compatibility across platforms, we enforce that spans are decoded as `u32`s first.

        let start = AtomParsableWrapper::<u32>::parse(ctx, db, start)?.0;
        let end = AtomParsableWrapper::<u32>::parse(ctx, db, end)?.0;

        Ok((start as usize)..(end as usize))
    }
}

impl SexprAtomParsable for Str {
    fn parse_atom(db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        Ok(db.intern_string_data(text))
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
pub type Name = Node<Str>;

impl SexprParsable for Name {
    fn parse(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        node: SexprNode,
    ) -> Result<Self, ParseError> {
        match node.contents {
            SexprNodeContents::Atom(text) => Ok(Node::new(node.span, db.intern_string_data(text))),
            SexprNodeContents::List(entries) => {
                let name = if let Some(first) = entries.first() {
                    match &first.contents {
                        SexprNodeContents::Atom(text) => {
                            Node::new(node.span, db.intern_string_data(text.to_string()))
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
                    ctx.process_name_info(db, &name, info)?;
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
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| Name::parse(ctx, db, arg))
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
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Ok(Self(ListParsableWrapper::parse(ctx, db, value)?.0))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnIndex(u32);

impl SexprAtomParsable for DeBruijnIndex {
    fn parse_atom(db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        u32::parse_atom(db, text).map(Self)
    }
}
