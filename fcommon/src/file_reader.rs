use std::{
    collections::HashMap,
    fmt::Debug,
    path::PathBuf,
    sync::{Arc, RwLock},
};

use crate::{Dr, InternExt, Report, ReportKind, Source};

/// Contains the contents of files that we do not wish to read from disk.
#[derive(Default)]
pub struct OverwrittenFiles {
    file_contents: HashMap<Source, String>,
}

impl Debug for OverwrittenFiles {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<owf>")
    }
}

impl OverwrittenFiles {
    /// Tell the database that we want to overwrite the contents of this file with the particular
    /// file contents provided.
    pub fn overwrite_file(&mut self, db: &mut dyn FileReader, source: Source, contents: String) {
        self.file_contents.insert(source, contents);
        SourceQuery.in_db_mut(db).invalidate(&source);
    }

    /// Tell the database that we no longer want to overwrite the contents of this file.
    /// The next time we need the file's contents, they will be read from disk.
    pub fn undo_overwrite_file(&mut self, db: &mut dyn FileReader, source: Source) {
        self.file_contents.remove(&source);
        SourceQuery.in_db_mut(db).invalidate(&source);
    }
}

#[salsa::query_group(FileReaderStorage)]
pub trait FileReader: InternExt + FileWatcher {
    /// Should be an absolute folder path.
    #[salsa::input]
    fn project_root(&self) -> Arc<PathBuf>;

    /// Call functions on this in order to overwrite contents of files as seen by the database.
    #[salsa::input]
    fn overwritten_files(&self) -> Arc<RwLock<OverwrittenFiles>>;

    /// Loads source code from a file.
    /// This is performed lazily when needed (see [`FileWatcher`]).
    fn source(&self, file_name: Source) -> Dr<Arc<String>>;
}

/// A trait to be implemented by databases which
/// signals that the database can listen for file updates.
pub trait FileWatcher {
    /// Register a path to be watched.
    /// This is recursive: if a path representing a directory is given, its children will also be watched.
    fn watch(&self, source: Source);
    /// This is called when a file was changed.
    /// This should invalidate the database's known information for files at this path.
    fn did_change_file(&mut self, source: Source);
}

#[tracing::instrument(level = "debug")]
fn source(db: &dyn FileReader, source: Source) -> Dr<Arc<String>> {
    db.salsa_runtime()
        .report_synthetic_read(salsa::Durability::LOW);

    if let Some(overwriten_contents) = &db
        .overwritten_files()
        .read()
        .unwrap()
        .file_contents
        .get(&source)
    {
        Dr::ok(Arc::new((*overwriten_contents).to_owned()))
    } else {
        db.watch(source);
        let path_buf = db
            .project_root()
            .join(db.path_to_path_buf(source.path))
            .with_extension(source.ty.extension());
        match std::fs::read_to_string(&path_buf) {
            Ok(value) => Dr::ok(value).map(Arc::new),
            Err(err) => Dr::fail(Report::new_in_file(ReportKind::Error, source).with_message(
                format!(
                    "could not read file '{}': {}",
                    path_buf.to_string_lossy(),
                    err,
                ),
            )),
        }
    }
}
