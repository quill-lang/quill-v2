use std::{
    fmt::Debug,
    sync::{mpsc, Arc, Mutex, RwLock},
    time::Duration,
};

use fcommon::*;
use fkernel::TypeCheckerStorage;
use fnodes::SexprParserStorage;
use notify::{RecommendedWatcher, Watcher};
use qelab::ElaboratorStorage;
use qparse::QuillParserStorage;
use salsa::Snapshot;

/// The main database that manages all the compiler's queries.
#[salsa::database(
    FileReaderStorage,
    InternStorage,
    QuillParserStorage,
    SexprParserStorage,
    TypeCheckerStorage,
    ElaboratorStorage
)]
pub struct QuillDatabase {
    storage: salsa::Storage<Self>,
    watcher: Arc<Mutex<RecommendedWatcher>>,
}

impl Debug for QuillDatabase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<db>")
    }
}

impl salsa::Database for QuillDatabase {}
impl salsa::ParallelDatabase for QuillDatabase {
    fn snapshot(&self) -> Snapshot<Self> {
        Snapshot::new(QuillDatabase {
            storage: self.storage.snapshot(),
            watcher: Arc::clone(&self.watcher),
        })
    }
}

impl FileWatcher for QuillDatabase {
    fn watch(&self, src: Source) {
        // Add a path to be watched. All files and directories at that path and
        // below will be monitored for changes.
        let mut watcher = self.watcher.lock().unwrap();
        // If we couldn't find the file for whatever reason,
        // the compilation step reading this file will fail anyway.
        // So we can safely ignore watching this path.
        // TODO: Watch parent paths to check if this file is ever created.
        let _ = watcher.watch(
            self.path_to_path_buf(src.path)
                .with_extension(src.ty.extension()),
            notify::RecursiveMode::Recursive,
        );
    }

    fn did_change_file(&mut self, src: Source) {
        SourceQuery.in_db_mut(self).invalidate(&src);
    }
}

impl QuillDatabase {
    /// Returns the database, along with a receiver for file update events.
    /// If running as a language server, this channel should be watched,
    /// and any updated paths should be passed into [`FileWatcher::did_change_file`].
    /// If running as a standalone compiler, the channel may be ignored,
    /// although receiving file update events may still be desirable in certain cases.
    pub fn new() -> (Self, mpsc::Receiver<notify::DebouncedEvent>) {
        let (tx, rx) = mpsc::channel();
        let mut this = Self {
            storage: Default::default(),
            watcher: Arc::new(Mutex::new(
                notify::watcher(tx, Duration::from_secs(1)).unwrap(),
            )),
        };
        this.set_overwritten_files_with_durability(
            Arc::new(RwLock::new(Default::default())),
            salsa::Durability::HIGH,
        );
        (this, rx)
    }
}
