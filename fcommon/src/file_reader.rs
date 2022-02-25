use std::sync::Arc;

use crate::{interning::Path, InternExt};

#[salsa::query_group(FileReaderStorage)]
pub trait FileReader: InternExt {
    #[salsa::input]
    fn project_root(&self) -> Arc<String>;

    /// Loads source code from a file.
    #[salsa::input]
    fn source(&self, file_name: Path) -> String;
}

pub trait FileReaderExt: FileReader {
    fn set_source_from_disk(&mut self, file_name: Path) {
        let path = self.path_to_path_buf(file_name);
        let src = std::fs::read_to_string(path).expect("could not read file");
        self.set_source(file_name, src);
    }
}

impl<T> FileReaderExt for T where T: FileReader {}
