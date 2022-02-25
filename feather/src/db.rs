use fcommon::*;

#[salsa::database(FileReaderStorage, InternStorage)]
#[derive(Default)]
pub struct FeatherDatabase {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for FeatherDatabase {}
