//! Feather's kernel.
//!
//! This is heavily inspired by the Lean 3 kernel: <https://github.com/leanprover/lean/blob/master/src/kernel>.

#![feature(let_chains)]

use std::{collections::HashMap, fmt::Debug, sync::Arc};

use fcommon::{Dr, PathData, Source};
use fnodes::{basic_nodes::Provenance, inductive::Inductive, module::Item};
use typeck::{CertifiedDefinition, Environment};

// Expose this either when we're running `cargo doc` or executing tests.
#[cfg(any(test, doc))]
mod test_db;

pub mod expr;
pub mod inductive;
pub mod typeck;
pub mod universe;

#[salsa::query_group(TypeCheckerStorage)]
pub trait TypeChecker: fnodes::SexprParserExt {
    /// Attempts to load the feather module from the given source and certify it as type correct.
    fn certify(&self, source: Source) -> Dr<Arc<CertifiedModule>>;
}

/// A module containing certified definitions and inductive definitions.
#[derive(PartialEq, Eq, Hash)]
pub struct CertifiedModule {
    /// The origin of the module in code.
    provenance: Provenance,
    pub defs: Vec<CertifiedDefinition>,
}

impl Debug for CertifiedModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified module")
    }
}

#[tracing::instrument(level = "trace")]
fn certify(db: &dyn TypeChecker, source: Source) -> Dr<Arc<CertifiedModule>> {
    let source_path = db.lookup_intern_path_data(source.path);
    db.module_from_feather_source(source).bind(|module| {
        let mut definitions = Vec::<CertifiedDefinition>::new();
        let mut reports = Vec::new();
        for item in &module.contents.items {
            let env = Environment {
                source,
                db: db.up(),
                definitions: {
                    let mut defs = HashMap::new();
                    for def in &definitions {
                        let mut new_path_data = source_path.clone();
                        new_path_data.0.push(def.def().contents.name.contents);
                        let path = db.intern_path_data(new_path_data);
                        defs.insert(path, def);
                    }
                    defs
                },
                inductives: HashMap::new(),
            };
            match item {
                Item::Definition(def) => {
                    let (result, more_reports) = typeck::check(&env, &def).destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        definitions.push(result);
                    }
                }
                Item::Inductive(ind) => {
                    let (result, more_reports) =
                        inductive::check_inductive_type(env, ind).destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        tracing::info!("{:#?}", result);
                        definitions.push(result.type_declaration);
                        for intro_rule in result.intro_rules {
                            definitions.push(intro_rule);
                        }
                    }
                }
            }
        }
        Dr::ok_with_many(
            Arc::new(CertifiedModule {
                provenance: module.provenance.clone(),
                defs: definitions,
            }),
            reports,
        )
    })
}
