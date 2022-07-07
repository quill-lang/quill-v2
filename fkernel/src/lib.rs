//! Feather's kernel.
//!
//! This is heavily inspired by the Lean 3 kernel: <https://github.com/leanprover/lean/blob/master/src/kernel>.

#![feature(let_chains)]

use std::{collections::HashMap, fmt::Debug, sync::Arc};

use fcommon::{Dr, Source};
use fnodes::{basic_nodes::Provenance, module::Item};
use inductive::CertifiedInductive;
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
    pub definitions: Vec<CertifiedDefinition>,
    pub inductives: Vec<CertifiedInductive>,
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
        let mut inductives = Vec::<CertifiedInductive>::new();
        let mut reports = Vec::new();
        for item in &module.contents.items {
            let mut local_definitions = HashMap::new();
            for def in &definitions {
                let mut new_path_data = source_path.clone();
                new_path_data.0.push(def.def().contents.name.contents);
                let path = db.intern_path_data(new_path_data);
                local_definitions.insert(path, def);
            }

            let mut local_inductives = HashMap::new();
            for ind in &inductives {
                let mut new_path_data = source_path.clone();
                new_path_data.0.push(ind.inductive().contents.name.contents);
                let path = db.intern_path_data(new_path_data);
                local_inductives.insert(path, ind);
            }

            match item {
                Item::Definition(def) => {
                    let env = Environment {
                        source,
                        db: db.up(),
                        definitions: local_definitions,
                        inductives: local_inductives,
                        universe_variables: &def.contents.universe_params,
                    };
                    let (result, more_reports) = typeck::check(&env, def).destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        definitions.push(result);
                    }
                }
                Item::Inductive(ind) => {
                    let env = Environment {
                        source,
                        db: db.up(),
                        definitions: local_definitions,
                        inductives: local_inductives,
                        universe_variables: &ind.contents.universe_params,
                    };
                    let (result, more_reports) =
                        inductive::check_inductive_type(env, ind).destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        // tracing::info!("{:#?}", result);
                        definitions.push(result.type_declaration);
                        for intro_rule in result.intro_rules {
                            definitions.push(intro_rule);
                        }
                        definitions.push(result.recursor);
                        inductives.push(result.inductive);
                    }
                }
            }
        }
        Dr::ok_with_many(
            Arc::new(CertifiedModule {
                provenance: module.provenance.clone(),
                definitions,
                inductives,
            }),
            reports,
        )
    })
}
