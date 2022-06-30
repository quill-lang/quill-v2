use std::collections::HashMap;

use fcommon::{Intern, Path, Source};
use fnodes::{definition::Definition, inductive::Inductive, SexprParser};

/// A typing environment, normally called capital gamma in the literature.
/// Contains information about everything we can see in the current position in a file.
pub struct Environment<'a> {
    pub source: Source,
    pub db: &'a dyn SexprParser,
    pub definitions: HashMap<Path, &'a Definition>,
    pub inductives: HashMap<Path, &'a Inductive>,
}
