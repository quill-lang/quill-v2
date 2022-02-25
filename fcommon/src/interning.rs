use std::path::PathBuf;

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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PathData(pub Vec<Str>);

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

impl Path {
    pub fn lookup(&self, db: &dyn Intern) -> PathData {
        db.lookup_intern_path_data(*self)
    }

    pub fn to_path_buf(&self, db: &dyn Intern) -> PathBuf {
        db.lookup_intern_path_data(*self)
            .0
            .into_iter()
            .map(|x| x.lookup(db))
            .collect()
    }
}
