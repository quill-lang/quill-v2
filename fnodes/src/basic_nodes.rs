use fcommon::{Path, PathData, Span, Str};

use crate::*;

impl ListSexpr for Span {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [start, end] = force_arity(span, args)?;

        // For the sake of compatibility across platforms, we enforce that spans are decoded as `u32`s first.

        let start = AtomicSexprWrapper::<u32>::parse(ctx, db, start)?;
        let end = AtomicSexprWrapper::<u32>::parse(ctx, db, end)?;

        Ok((start as usize)..(end as usize))
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(ctx, db, &(self.start as u32)),
            AtomicSexprWrapper::serialise_into_node(ctx, db, &(self.end as u32)),
        ]
    }
}

impl AtomicSexpr for String {
    fn parse_atom(_db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        Ok(text)
    }

    fn serialise(&self, _ctx: &SexprSerialiseContext, _db: &dyn SexprParser) -> String {
        self.clone()
    }
}

impl AtomicSexpr for Str {
    fn parse_atom(db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        Ok(db.intern_string_data(text))
    }

    fn serialise(&self, _ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> String {
        db.lookup_intern_string_data(*self)
    }
}

/// This impl is provided for symmetry with the impls of [`Name`].
impl SexprParsable for Str {
    type Output = Str;

    fn parse(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        node: SexprNode,
    ) -> Result<Self::Output, ParseError> {
        AtomicSexprWrapper::parse(ctx, db, node)
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
pub type Name = Node<Str>;

impl SexprParsable for Name {
    type Output = Self;

    fn parse(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        node: SexprNode,
    ) -> Result<Self, ParseError> {
        match node.contents {
            SexprNodeContents::Atom(text) => Ok(Node::new(
                ctx.node_id_gen.gen(),
                node.span,
                db.intern_string_data(text),
            )),
            SexprNodeContents::List(entries) => {
                let name = if let Some(first) = entries.first() {
                    match &first.contents {
                        SexprNodeContents::Atom(text) => Node::new(
                            ctx.node_id_gen.gen(),
                            node.span,
                            db.intern_string_data(text.to_string()),
                        ),
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

impl SexprSerialisable for Name {
    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> SexprNode {
        // TODO: serialise infos
        AtomicSexprWrapper::serialise_into_node(ctx, db, &self.contents)
    }
}

impl<T> ListSexpr for Vec<T>
where
    T: ListSexpr,
{
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| ListSexprWrapper::parse(ctx, db, arg))
            .collect()
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter()
            .map(|name| ListSexprWrapper::serialise_into_node(ctx, db, name))
            .collect()
    }
}

impl ListSexpr for Vec<Str> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| AtomicSexprWrapper::parse(ctx, db, arg))
            .collect()
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter()
            .map(|name| AtomicSexprWrapper::serialise_into_node(ctx, db, name))
            .collect()
    }
}

impl ListSexpr for Vec<Name> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| Name::parse(ctx, db, arg))
            .collect()
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter().map(|name| name.serialise(ctx, db)).collect()
    }
}

/// A qualified name that may have been written in code, rather than one simply stored internally
/// that was never written in code (see [`fcommon::Path`] for that use case).
#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedName(pub Vec<Name>);

impl ListSexpr for QualifiedName {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        ListSexpr::parse_list(ctx, db, span, args).map(Self)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.0.serialise(ctx, db)
    }
}

impl ListSexpr for Path {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        ListSexpr::parse_list(ctx, db, span, args).map(|list| db.intern_path_data(PathData(list)))
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        db.lookup_intern_path_data(*self).0.serialise(ctx, db)
    }
}

/// Specifies where in source (Quill) code a node came from.
/// This is often used in names and expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSpan(pub Span);

impl PartialOrd for SourceSpan {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SourceSpan {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .start
            .cmp(&other.0.start)
            .then(self.0.end.cmp(&other.0.end))
    }
}

impl ListSexpr for SourceSpan {
    const KEYWORD: Option<&'static str> = Some("at");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        ListSexprWrapper::parse(ctx, db, value).map(Self)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![ListSexprWrapper::serialise_into_node(ctx, db, &self.0)]
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnIndex(pub u32);

impl AtomicSexpr for DeBruijnIndex {
    fn parse_atom(db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        u32::parse_atom(db, text).map(Self)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> String {
        self.0.serialise(ctx, db)
    }
}

/// A documentation string.
/// Even though this isn't a single identifier, it's still represented as a [Name].
#[derive(Debug, PartialEq, Eq)]
pub struct Documentation(pub Name);

impl ListSexpr for Documentation {
    const KEYWORD: Option<&'static str> = Some("doc");

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Name::parse(ctx, db, value).map(Self)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![self.0.serialise(ctx, db)]
    }
}
