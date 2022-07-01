use std::collections::HashMap;

use fcommon::{Intern, Path, Source};
use fnodes::{definition::Definition, inductive::Inductive, SexprParser};

/// A typing environment, normally called capital gamma in the literature.
/// Contains information about everything we can see in the current position in a file.
pub struct Environment<'a> {
    pub source: Source,
    pub db: &'a dyn SexprParser,
    pub definitions: HashMap<Path, EnvironmentDefinition<'a>>,
    pub inductives: HashMap<Path, &'a Inductive>,
}

pub struct EnvironmentDefinition<'a> {
    pub def: &'a Definition,
    pub reducibility: ReducibilityHints,
}

/// Hints used by the definitional equality checker to choose which definitions to unfold first.
/// In particular, if we are checking if `f x y z` is equal to `g a b c`, we look at the
/// reducibility hints of `f` and `g`. If one has a heigher height than the other, we unfold
/// that one first, as it may reduce into an invocation of the other function. This essentially
/// allows us to unfold complicated expressions into easier ones, rather than having to unfold
/// all expressions into normal form, which would be very computationally intensive.
pub enum ReducibilityHints {
    Regular {
        height: DefinitionHeight,
    },
    /// Opaque definitions are never unfolded.
    /// They do not have a definition height.
    Opaque,
}

/// If this number is higher, the definition is 'more complex'.
/// We define the height of a [`ReducibilityHints::Regular`] definition to be one more than
/// the maximum height of any [`ReducibilityHints::Regular`] definitions it contains.
pub type DefinitionHeight = u64;
