use std::{path::PathBuf, sync::Arc};

use crate::{interning::Path, InternExt};

#[salsa::query_group(FileReaderStorage)]
pub trait FileReader: InternExt + FileWatcher {
    /// Should be an absolute folder path.
    #[salsa::input]
    fn project_root(&self) -> Arc<PathBuf>;

    /// Loads source code from a file.
    /// This is performed lazily when needed (see [`FileWatcher`]).
    fn source(&self, file_name: Path) -> String;
}

/// A trait to be implemented by databases which
/// signals that the database can listen for file updates.
pub trait FileWatcher {
    /// Register a path to be watched.
    /// This is recursive: if a path representing a directory is given, its children will also be watched.
    fn watch(&self, path: Path);
    /// This is called when a file was changed.
    /// This should invalidate the database's known information for files at this path.
    fn did_change_file(&mut self, path: Path);
}

fn source(db: &dyn FileReader, path: Path) -> String {
    db.salsa_runtime()
        .report_synthetic_read(salsa::Durability::LOW);

    db.watch(path);
    let path_buf = db.project_root().join(db.path_to_path_buf(path));
    std::fs::read_to_string(&path_buf).unwrap_or_default()
}
