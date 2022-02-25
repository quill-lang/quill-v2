use std::{
    sync::{mpsc, Arc, Mutex},
    time::Duration,
};

use fcommon::*;
use notify::{RecommendedWatcher, Watcher};
use salsa::Snapshot;

/// The main database that manages all the compiler's queries.
#[salsa::database(FileReaderStorage, InternStorage)]
pub struct FeatherDatabase {
    storage: salsa::Storage<Self>,
    watcher: Arc<Mutex<RecommendedWatcher>>,
}

impl salsa::Database for FeatherDatabase {}
impl salsa::ParallelDatabase for FeatherDatabase {
    fn snapshot(&self) -> Snapshot<Self> {
        Snapshot::new(FeatherDatabase {
            storage: self.storage.snapshot(),
            watcher: Arc::clone(&self.watcher),
        })
    }
}

impl FileWatcher for FeatherDatabase {
    fn watch(&self, path: Path) {
        // Add a path to be watched. All files and directories at that path and
        // below will be monitored for changes.
        let mut watcher = self.watcher.lock().unwrap();
        watcher
            .watch(
                self.path_to_path_buf(path),
                notify::RecursiveMode::Recursive,
            )
            .unwrap();
    }

    fn did_change_file(&mut self, path: Path) {
        SourceQuery.in_db_mut(self).invalidate(&path);
    }
}

impl FeatherDatabase {
    /// Returns the database, along with a receiver for file update events.
    /// If running as a language server, this channel should be watched,
    /// and any updated paths should be passed into [`FileWatcher::did_change_file`].
    /// If running as a standalone compiler, the channel may be ignored,
    /// although receiving file update events may still be desirable in certain cases.
    pub fn new() -> (Self, mpsc::Receiver<notify::DebouncedEvent>) {
        let (tx, rx) = mpsc::channel();

        (
            Self {
                storage: Default::default(),
                watcher: Arc::new(Mutex::new(
                    notify::watcher(tx, Duration::from_secs(1)).unwrap(),
                )),
            },
            rx,
        )
    }
}
