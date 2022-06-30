// TODO: Document this module, taking care to detail each universe operation.

use crate::basic_nodes::*;
use crate::expr::*;
use crate::*;
use fcommon::Source;
use fcommon::{Span, Str};
use fnodes_macros::*;

/// A concrete universe level.
/// Level `0` represents `Prop`, the type of (proof-irrelevant) propositions.
/// Level `1` represents `Type`, the type of all (small) types.
pub type UniverseLevel = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univzero"]
pub struct UniverseZero;

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univvar"]
pub struct UniverseVariable(#[atomic] pub Str);

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univsucc"]
pub struct UniverseSucc(#[list] pub Box<Universe>);

/// Takes the larger universe of `left` and `right`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univmax"]
pub struct UniverseMax {
    #[list]
    pub left: Box<Universe>,
    #[list]
    pub right: Box<Universe>,
}

/// Takes the larger universe of `left` and `right`, but if `right == 0`, then this just gives `0`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univimax"]
pub struct UniverseImpredicativeMax {
    #[list]
    pub left: Box<Universe>,
    #[list]
    pub right: Box<Universe>,
}

/// An inference variable for universes.
/// May represent any universe.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "univmeta"]
pub struct Metauniverse(#[atomic] u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UniverseContents {
    UniverseZero,
    UniverseVariable(UniverseVariable),
    UniverseSucc(UniverseSucc),
    UniverseMax(UniverseMax),
    UniverseImpredicativeMax(UniverseImpredicativeMax),
    Metauniverse(Metauniverse),
}

impl UniverseContents {
    fn variant_keyword(&self) -> &'static str {
        match self {
            Self::UniverseZero => UniverseZero::KEYWORD.unwrap(),
            Self::UniverseVariable(_) => UniverseVariable::KEYWORD.unwrap(),
            Self::UniverseSucc(_) => UniverseSucc::KEYWORD.unwrap(),
            Self::UniverseMax(_) => UniverseMax::KEYWORD.unwrap(),
            Self::UniverseImpredicativeMax(_) => UniverseImpredicativeMax::KEYWORD.unwrap(),
            Self::Metauniverse(_) => Metauniverse::KEYWORD.unwrap(),
        }
    }
}

impl ListSexpr for UniverseContents {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.is_empty() {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                    expected: "<any universe>",
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
                    expected: "<any universe>",
                },
            });
        };

        // Reduce the span to only contain the arguments, not the keyword.
        let span = (first.span.end + 1)..span.end - 1;

        Ok(match Some(keyword) {
            UniverseZero::KEYWORD => Self::UniverseZero,
            UniverseVariable::KEYWORD => {
                Self::UniverseVariable(UniverseVariable::parse_list(db, source, span, args)?)
            }
            UniverseSucc::KEYWORD => {
                Self::UniverseSucc(UniverseSucc::parse_list(db, source, span, args)?)
            }
            UniverseMax::KEYWORD => {
                Self::UniverseMax(UniverseMax::parse_list(db, source, span, args)?)
            }
            UniverseImpredicativeMax::KEYWORD => Self::UniverseImpredicativeMax(
                UniverseImpredicativeMax::parse_list(db, source, span, args)?,
            ),
            Metauniverse::KEYWORD => {
                Self::Metauniverse(Metauniverse::parse_list(db, source, span, args)?)
            }
            _ => {
                return Err(ParseError {
                    span: first.span.clone(),
                    reason: ParseErrorReason::WrongKeyword {
                        expected: "<any universe>",
                        found: keyword.to_string(),
                    },
                })
            }
        })
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: expr infos
        let mut result = match self {
            Self::UniverseZero => UniverseZero.serialise(db),
            Self::UniverseVariable(val) => val.serialise(db),
            Self::UniverseSucc(val) => val.serialise(db),
            Self::UniverseMax(val) => val.serialise(db),
            Self::UniverseImpredicativeMax(val) => val.serialise(db),
            Self::Metauniverse(val) => val.serialise(db),
        };
        result.insert(
            0,
            SexprNode {
                contents: SexprNodeContents::Atom(self.variant_keyword().to_owned()),
                span: 0..0,
            },
        );
        result
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Universe {
    pub provenance: Provenance,
    pub contents: UniverseContents,
}

impl std::fmt::Debug for Universe {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:?}@{:#?}", self.provenance, self.contents)
        } else {
            write!(f, "{:?}@{:?}", self.provenance, self.contents)
        }
    }
}

impl Universe {
    pub fn new_in_sexpr(source: Source, span: Span, contents: UniverseContents) -> Self {
        Self {
            provenance: Provenance::Sexpr { source, span },
            contents,
        }
    }

    pub fn new_synthetic(contents: UniverseContents) -> Self {
        Self {
            provenance: Provenance::Synthetic,
            contents,
        }
    }

    pub fn new_with_provenance(provenance: &Provenance, contents: UniverseContents) -> Self {
        Self {
            provenance: provenance.clone(),
            contents,
        }
    }

    /// Compares two universes for equality, ignoring provenance data.
    pub fn eq_ignoring_provenance(&self, other: &Universe) -> bool {
        match (&self.contents, &other.contents) {
            (UniverseContents::UniverseZero, UniverseContents::UniverseZero) => true,
            (UniverseContents::UniverseVariable(_), UniverseContents::UniverseVariable(_)) => {
                todo!()
            }
            (UniverseContents::UniverseSucc(arg1), UniverseContents::UniverseSucc(arg2)) => {
                arg1.0.eq_ignoring_provenance(&arg2.0)
            }
            (UniverseContents::UniverseMax(arg1), UniverseContents::UniverseMax(arg2)) => {
                arg1.left.eq_ignoring_provenance(&arg2.left)
                    && arg1.right.eq_ignoring_provenance(&arg2.right)
            }
            (
                UniverseContents::UniverseImpredicativeMax(arg1),
                UniverseContents::UniverseImpredicativeMax(arg2),
            ) => {
                arg1.left.eq_ignoring_provenance(&arg2.left)
                    && arg1.right.eq_ignoring_provenance(&arg2.right)
            }
            (UniverseContents::Metauniverse(arg1), UniverseContents::Metauniverse(arg2)) => {
                arg1.0 == arg2.0
            }
            _ => false,
        }
    }

    /// Returns a dummy universe.
    /// Should not be used for anything.
    pub fn dummy() -> Universe {
        Self::new_synthetic(UniverseContents::UniverseZero)
    }
}

impl ListSexpr for Universe {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        UniverseContents::parse_list(db, source, span.clone(), args)
            .map(|univ_contents| Universe::new_in_sexpr(source, span, univ_contents))
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.contents.serialise(db)
    }
}

impl Universe {
    /// If this universe is syntactically equal to `Sort k` for some integer `k`, return `k`.
    pub fn to_explicit_universe(&self) -> Option<UniverseLevel> {
        match &self.contents {
            UniverseContents::UniverseZero => Some(0),
            UniverseContents::UniverseSucc(inner) => inner.0.to_explicit_universe().map(|n| n + 1),
            _ => None,
        }
    }
}
