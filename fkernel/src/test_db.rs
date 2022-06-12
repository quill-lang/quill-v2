//! A test harness for unit tests that require a salsa database.
//! This is enabled only when we're running tests.

use std::sync::Arc;

use fcommon::*;
use fnodes::SexprParserStorage;
use salsa::Durability;

/// A dummy single-threaded database that does not reach out to disk.
/// File contents are updated manually.
#[derive(Default)]
#[salsa::database(FileReaderStorage, InternStorage, SexprParserStorage)]
pub struct TestDatabase {
    storage: salsa::Storage<Self>,
}

impl std::fmt::Debug for TestDatabase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<db>")
    }
}

impl salsa::Database for TestDatabase {}

/// The database does not actually read any files from disk.
/// Hence, it does not actually need to watch any files.
impl FileWatcher for TestDatabase {
    fn watch(&self, _: Source) {}
    fn did_change_file(&mut self, _: Source) {}
}

/// Creates a test database that contains one file with the given contents.
/// This database will not reach out to files on disk.
/// Returns a database and the [`Source`] referencing the file that was created.
pub fn database_with_file(
    file_name: Vec<&str>,
    source_type: SourceType,
    contents: &str,
) -> (TestDatabase, Source) {
    let mut db = TestDatabase::default();
    db.set_no_read_from_disk_with_durability(true, Durability::HIGH);
    let source = Source {
        path: db.intern_path_data(PathData(
            file_name
                .iter()
                .map(|segment| db.intern_string_data(segment.to_string()))
                .collect(),
        )),
        ty: source_type,
    };
    db.set_overwritten_file_contents_with_durability(
        source,
        Arc::new(contents.to_owned()),
        Durability::HIGH,
    );
    (db, source)
}
