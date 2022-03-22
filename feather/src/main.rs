use std::{collections::HashSet, path::PathBuf, sync::Arc};

use fcommon::{FileReader, Intern, InternExt, PathData, Source, SourceType};
use fnodes::{ListSexprWrapper, PrettyPrintSettings, SexprSerialiseContext, SexprSerialiseExt};
use fvalue::ValueInferenceEngine;
use salsa::Durability;
use tracing::info;
use tracing_subscriber::{fmt::format::FmtSpan, FmtSubscriber};

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
        ty: SourceType::Feather,
    };

    let result = db.infer_values(source);
    for report in result.reports() {
        report.render(&db);
    }

    if let Some(result) = result.value() {
        let mut ctx = SexprSerialiseContext::default();
        ctx.register_expr_info(&result.infos.expr_at);
        ctx.register_expr_info(&result.infos.expr_ty);
        ctx.register_name_info(&result.infos.name_at);
        let node = ListSexprWrapper::serialise_into_node(&ctx, &db, &*result.module);
        let pretty_print = PrettyPrintSettings {
            no_indent_for: {
                let mut map = HashSet::new();
                for s in ["local", "iu64", "iunit", "fu64", "funit", "funiverse"] {
                    map.insert(s.to_string());
                }
                map
            },
        };
        std::fs::write(
            db.path_to_path_buf(path).with_extension("tyck.sexp"),
            node.to_string(&pretty_print),
        )
        .unwrap();
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
