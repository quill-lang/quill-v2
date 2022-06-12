use std::{path::PathBuf, sync::Arc};

use crate::{Dr, InternExt, Report, ReportKind, Source};

#[salsa::query_group(FileReaderStorage)]
pub trait FileReader: InternExt + FileWatcher {
    /// Should be an absolute folder path.
    #[salsa::input]
    fn project_root(&self) -> Arc<PathBuf>;

    /// If this is true, the file reader will never read files from disk.
    /// Instead, it will only return overwritten copies of files.
    /// This means that the runtime will panic if we try to read a file that
    /// has not been overwritten by `overwritten_file_contents`.
    #[salsa::input]
    fn no_read_from_disk(&self) -> bool;

    /// Edit this input to overwrite the output provided by `source`.
    /// The overwritten files are only read if `no_read_from_disk` is true.
    #[salsa::input]
    fn overwritten_file_contents(&self, file_name: Source) -> Arc<String>;

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

    if db.no_read_from_disk() {
        Dr::ok(db.overwritten_file_contents(source))
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
