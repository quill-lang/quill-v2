use std::{fmt::Display, ops::Add};

use fcommon::{Intern, Path, PathData, Source, Span, Str};

use crate::*;

impl ListSexpr for Span {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [start, end] = force_arity(span, args)?;

        // For the sake of compatibility across platforms, we enforce that spans are decoded as `u32`s first.

        let start = AtomicSexprWrapper::<u32>::parse(db, source, start)?;
        let end = AtomicSexprWrapper::<u32>::parse(db, source, end)?;

        Ok((start as usize)..(end as usize))
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(db, &(self.start as u32)),
            AtomicSexprWrapper::serialise_into_node(db, &(self.end as u32)),
        ]
    }
}

/// The place the node came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Provenance {
    Sexpr { source: Source, span: Span },
    Synthetic,
}

impl Provenance {
    pub fn source(&self) -> Option<Source> {
        match self {
            Provenance::Sexpr { source, .. } => Some(*source),
            Provenance::Synthetic => None,
        }
    }

    /// Returns the span, or `0..0` if it was synthetic.
    pub fn span(&self) -> Span {
        match self {
            Provenance::Sexpr { span, .. } => span.clone(),
            Provenance::Synthetic => 0..0,
        }
    }
}

impl AtomicSexpr for String {
    fn parse_atom(
        _db: &dyn SexprParser,
        source: Source,
        text: String,
    ) -> Result<Self, ParseErrorReason> {
        Ok(text)
    }

    fn serialise(&self, _db: &dyn SexprParser) -> String {
        self.clone()
    }
}

impl AtomicSexpr for Str {
    fn parse_atom(
        db: &dyn SexprParser,
        source: Source,
        text: String,
    ) -> Result<Self, ParseErrorReason> {
        Ok(db.intern_string_data(text))
    }

    fn serialise(&self, db: &dyn SexprParser) -> String {
        db.lookup_intern_string_data(*self)
    }
}

/// This impl is provided for symmetry with the impls of [`Name`].
impl SexprParsable for Str {
    type Output = Str;

    fn parse(
        db: &dyn SexprParser,
        source: Source,
        node: SexprNode,
    ) -> Result<Self::Output, ParseError> {
        AtomicSexprWrapper::parse(db, source, node)
    }
}

/// This impl is provided for symmetry with the impls of [`Name`].
impl SexprSerialisable for Str {
    fn serialise(&self, db: &dyn SexprParser) -> SexprNode {
        AtomicSexprWrapper::serialise_into_node(db, self)
    }
}

/// A single indivisible lexical unit in an identifier, variable, or so on.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Name {
    /// The origin of the expression.
    pub provenance: Provenance,
    /// The actual contents of this expression.
    pub contents: Str,
}

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.provenance, self.contents)
    }
}

impl SexprParsable for Name {
    type Output = Self;

    fn parse(db: &dyn SexprParser, source: Source, node: SexprNode) -> Result<Self, ParseError> {
        match node.contents {
            SexprNodeContents::Atom(text) => Ok(Name {
                provenance: Provenance::Sexpr {
                    source,
                    span: node.span,
                },
                contents: db.intern_string_data(text),
            }),
            SexprNodeContents::List(entries) => {
                let name = if let Some(first) = entries.first() {
                    match &first.contents {
                        SexprNodeContents::Atom(text) => Name {
                            provenance: Provenance::Sexpr {
                                source,
                                span: node.span,
                            },
                            contents: db.intern_string_data(text.to_string()),
                        },
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
                    // TODO: node info
                    // ctx.process_name_info(db, &name, info)?;
                }

                Ok(name)
            }
        }
    }
}

impl SexprSerialisable for Name {
    fn serialise(&self, db: &dyn SexprParser) -> SexprNode {
        // TODO: node info
        // let mut infos = ctx.process_name_info(db, self, ctx);
        let serialised = AtomicSexprWrapper::serialise_into_node(db, &self.contents);
        // if infos.is_empty() {
        serialised
        // } else {
        //     infos.insert(0, serialised);
        //     SexprNode {
        //         contents: SexprNodeContents::List(infos),
        //         span: 0..0,
        //     }
        // }
    }
}

impl Name {
    /// Compares two names for equality, ignoring the provenance data.
    pub fn eq_ignoring_provenance(&self, other: &Name) -> bool {
        self.contents == other.contents
    }
}

impl<T> ListSexpr for Vec<T>
where
    T: ListSexpr,
{
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| ListSexprWrapper::parse(db, source, arg))
            .collect()
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter()
            .map(|name| ListSexprWrapper::serialise_into_node(db, name))
            .collect()
    }
}

impl ListSexpr for Vec<Str> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| AtomicSexprWrapper::parse(db, source, arg))
            .collect()
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter()
            .map(|name| AtomicSexprWrapper::serialise_into_node(db, name))
            .collect()
    }
}

impl ListSexpr for Vec<Name> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        _span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        args.into_iter()
            .map(|arg| Name::parse(db, source, arg))
            .collect()
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.iter().map(|name| name.serialise(db)).collect()
    }
}

/// A qualified name that may have been written in code, rather than one simply stored internally
/// that was never written in code (see [`fcommon::Path`] for that use case).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct QualifiedName {
    /// The origin of the expression.
    pub provenance: Provenance,
    /// The segments of the name, e.g. `["foo", "bar"]` in `foo::bar`.
    pub segments: Vec<Name>,
}

impl std::fmt::Debug for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.provenance, self.segments)
    }
}

impl QualifiedName {
    pub fn to_path(&self, intern: &dyn Intern) -> Path {
        intern.intern_path_data(PathData(
            self.segments.iter().map(|name| name.contents).collect(),
        ))
    }

    pub fn display(&self, intern: &dyn Intern) -> String {
        self.to_path(intern).display(intern)
    }
}

impl ListSexpr for QualifiedName {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        ListSexpr::parse_list(db, source, span.clone(), args).map(|list| Self {
            provenance: Provenance::Sexpr { source, span },
            segments: list,
        })
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.segments.serialise(db)
    }
}

impl ListSexpr for Path {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        ListSexpr::parse_list(db, source, span, args)
            .map(|list| db.intern_path_data(PathData(list)))
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        db.lookup_intern_path_data(*self).0.serialise(db)
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
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        ListSexprWrapper::parse(db, source, value).map(Self)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![ListSexprWrapper::serialise_into_node(db, &self.0)]
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnIndex(u32);

impl AtomicSexpr for DeBruijnIndex {
    fn parse_atom(
        db: &dyn SexprParser,
        source: Source,
        text: String,
    ) -> Result<Self, ParseErrorReason> {
        u32::parse_atom(db, source, text).map(Self)
    }

    fn serialise(&self, db: &dyn SexprParser) -> String {
        self.0.serialise(db)
    }
}

impl Display for DeBruijnIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl DeBruijnIndex {
    /// The lowest de Bruijn index.
    pub fn zero() -> DeBruijnIndex {
        Self(0)
    }

    /// The next (higher) de Bruijn index.
    pub fn succ(self) -> DeBruijnIndex {
        Self(self.0 + 1)
    }

    /// The previous (lower) de Bruijn index, or zero if one does not exist.
    pub fn pred(self) -> DeBruijnIndex {
        Self(self.0.saturating_sub(1))
    }
}

/// An offset for de Bruijn indices, which can be used to calculate relative indices.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnOffset(u32);

impl DeBruijnOffset {
    /// The zero offset.
    pub fn zero() -> DeBruijnOffset {
        Self(0)
    }

    /// Increase the offset by one.
    pub fn succ(self) -> DeBruijnOffset {
        Self(self.0 + 1)
    }
}

impl Add<DeBruijnOffset> for DeBruijnIndex {
    type Output = DeBruijnIndex;

    fn add(self, rhs: DeBruijnOffset) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

/// A documentation string.
/// Even though this isn't a single identifier, it's still represented as a [Name].
#[derive(Debug, PartialEq, Eq)]
pub struct Documentation(pub Name);

impl ListSexpr for Documentation {
    const KEYWORD: Option<&'static str> = Some("doc");

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        let [value] = force_arity(span, args)?;
        Name::parse(db, source, value).map(Self)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![self.0.serialise(db)]
    }
}
