use std::{path::PathBuf, sync::Arc};

use fcommon::{FileReader, Intern, PathData, Source, SourceType};
use fkernel::expr::ExprPrinter;
use fnodes::expr::{Expr, ExprContents};
use qelab::Elaborator;
use salsa::Durability;
use tracing::info;
use tracing_subscriber::{fmt::format::FmtSpan, FmtSubscriber};
use upcast::Upcast;

mod db;

fn main() {
    let log_level = tracing::Level::TRACE;
    let subscriber = FmtSubscriber::builder()
        .with_writer(std::io::stderr)
        .with_max_level(log_level)
        .with_span_events(FmtSpan::CLOSE)
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .pretty()
        .finish();
    tracing::subscriber::set_global_default(subscriber)
        .expect("could not set default tracing subscriber");
    info!("initialised logging with verbosity level {}", log_level);

    let (mut db, _rx) = db::FeatherDatabase::new();
    db.set_project_root_with_durability(Arc::new(PathBuf::new()), Durability::HIGH);
    let path = db.intern_path_data(PathData(vec![
        db.intern_string_data("test".to_string()),
        db.intern_string_data("test".to_string()),
    ]));
    let source = Source {
        path,
        ty: SourceType::Quill,
    };

    let result = db.elaborate_and_certify(source);
    // Use a locked version of `stderr`, so that reports are not interspersed
    // with other things such as tracing messages from other threads.
    let mut stderr = std::io::stderr().lock();
    for report in result.reports() {
        report.render(&db, &mut stderr);
    }

    if let Some(result) = result.value() {
        for def in &result.definitions {
            let mut printer = ExprPrinter::new(db.up());
            tracing::debug!(
                "certified definition {}\nsort: {}\ntype: {}\nvalue: {}\nreducibility hints: {}",
                db.lookup_intern_string_data(def.def().contents.name.contents),
                printer.print(&Expr::new_synthetic(ExprContents::Sort(def.sort().clone()))),
                printer.print(&def.def().contents.ty),
                def.def()
                    .contents
                    .expr
                    .as_ref()
                    .map(|e| printer.print(e))
                    .unwrap_or_else(|| "no body".to_string()),
                def.reducibility_hints()
            )
        }
        for ind in &result.inductives {
            tracing::debug!(
                "certified inductive {}",
                db.lookup_intern_string_data(ind.inductive().contents.name.contents),
            );
        }

        // let node = ListSexprWrapper::serialise_into_node(&db, &**result);
        // let pretty_print = PrettyPrintSettings {
        //     no_indent_for: {
        //         let mut map = HashSet::new();
        //         for s in ["local", "iu64", "iunit", "fu64", "funit", "funiverse"] {
        //             map.insert(s.to_string());
        //         }
        //         map
        //     },
        // };
        // std::fs::write(
        //     db.path_to_path_buf(path).with_extension("tyck.sexp"),
        //     node.to_string(&pretty_print),
        // )
        // .unwrap();
    }

    /*
    // This is the main loop for language servers, and other things that need regular file updates.
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
    */
}
