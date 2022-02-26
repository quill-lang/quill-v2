use std::path::PathBuf;

/// A span of code in a source file.
/// Represented by a range of UTF-8 characters.
pub type Span = std::ops::Range<usize>;

use salsa::{InternId, InternKey};
/// Provides utilities for interning various data types.
#[salsa::query_group(InternStorage)]
pub trait Intern {
    #[salsa::interned]
    fn intern_string_data(&self, data: String) -> Str;

    #[salsa::interned]
    fn intern_path_data(&self, data: PathData) -> Path;
}

/// An interned string type.
/// Can be safely copied and compared cheaply.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Str(InternId);

impl InternKey for Str {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

impl Str {
    pub fn lookup(&self, db: &dyn Intern) -> String {
        db.lookup_intern_string_data(*self)
    }
}

/// Uniquely identifies a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source {
    /// The relative path from the project root to this source file.
    /// File extensions are *not* appended to this path.
    pub path: Path,
    /// The type of the file.
    /// This is used to deduce the file extension.
    pub ty: SourceType,
}

/// Used to deduce the file extension of a [`Source`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SourceType {
    /// A feather source file, written as an S-expression encoded as UTF-8.
    Feather,
}

impl SourceType {
    pub fn extension(self) -> &'static str {
        match self {
            SourceType::Feather => "sexp",
        }
    }
}

/// A fully qualified path.
/// Use [`Path`] instead, if possible.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PathData(pub Vec<Str>);

/// A fully qualified path.
/// Can be used, for example, as a qualified name for a definition or for a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Path(InternId);

impl InternKey for Path {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

pub trait InternExt: Intern {
    fn path_data_to_path_buf(&self, data: &PathData) -> PathBuf {
        data.0
            .iter()
            .map(|x| self.lookup_intern_string_data(*x))
            .collect()
    }

    fn path_to_path_buf(&self, path: Path) -> PathBuf {
        self.path_data_to_path_buf(&self.lookup_intern_path_data(path))
    }
}
impl<T> InternExt for T where T: Intern {}
