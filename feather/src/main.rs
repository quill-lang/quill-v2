use std::{path::PathBuf, sync::Arc};

use fcommon::{FileReader, Intern, PathData, Source, SourceType};
use fnodes::SexprParser;
use salsa::Durability;

mod db;

fn main() {
    run(false);
}

fn run(watch_for_file_updates: bool) {
    let (mut db, rx) = db::FeatherDatabase::new();
    db.set_project_root_with_durability(Arc::new(PathBuf::new()), Durability::HIGH);
    let path = db.intern_path_data(PathData(vec![
        db.intern_string_data("test".to_string()),
        db.intern_string_data("test".to_string()),
    ]));
    let src = Source {
        path,
        ty: SourceType::Feather,
    };

    let result = db.expr_from_feather_source(src);
    for report in result.reports() {
        report.render(&db);
    }
    // println!("{:#?}", db.expr_from_feather_source(src));

    /*if watch_for_file_updates {
        loop {
            match rx.recv() {
                Ok(event) => {
                    println!("caught event {:?}", event);
                    if let notify::DebouncedEvent::Write(filepath_buf) = event {
                        // Convert this PathBuf into a rust Path, relativised to the current project directory.
                        if let Ok(path_relativised) = filepath_buf.strip_prefix(&*db.project_root())
                        {
                            // Convert this relativised rust Path into a feather Path.
                            let path = db.intern_path_data(PathData(
                                path_relativised
                                    .iter()
                                    .map(|component| {
                                        db.intern_string_data(
                                            component.to_string_lossy().to_string(),
                                        )
                                    })
                                    .collect(),
                            ));
                            // Tell the database that the file got changed.
                            println!("file '{}' changed", filepath_buf.to_string_lossy());
                            db.did_change_file(path);
                        } else {
                            // TODO: Add the tracing crate.
                            println!(
                                "ignoring file path '{}' outside the project root",
                                filepath_buf.to_string_lossy()
                            );
                        }
                    }
                }
                Err(e) => println!("watch error: {:?}", e),
            }
        }
    }*/
}
