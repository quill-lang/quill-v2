use fcommon::{FileReader, FileReaderExt, Intern, PathData};

mod db;

fn main() {
    let mut db = db::FeatherDatabase::default();
    let path = db.intern_path_data(PathData(vec![
        db.intern_string_data("test".to_string()),
        db.intern_string_data("test.sexp".to_string()),
    ]));
    db.set_source_from_disk(path);
    println!("{}", db.source(path));
}
