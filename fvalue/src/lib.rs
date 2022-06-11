//! Computes values of expressions and performs value inference.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use fcommon::{Dr, Path, Source, Str};
use fnodes::{
    basic_nodes::SourceSpan, expr::*, DefaultInfos, ModuleParseResult, NodeInfoContainer,
    SexprParserExt,
};
use tracing::debug;

#[salsa::query_group(ValueInferenceStorage)]
pub trait ValueInferenceEngine: SexprParserExt {
    /// Compute the definitions that each definition in this source file depends on.
    fn def_deps(&self, source: Source) -> Dr<BTreeMap<Str, BTreeSet<Path>>>;
    /// Compute the definitions that each definition in this module depends on,
    /// that were defined inside this module.
    fn local_def_deps(&self, source: Source) -> Dr<BTreeMap<Str, BTreeSet<Str>>>;
    /// Computes an order in which to infer types, such that we never run into circular dependencies.
    /// In particular, if definitions A and B reference each other, at least one of them must have an externally
    /// declared type; they cannot both have an inferred types.
    ///
    /// Note that it is allowed to use external instances of symbols only if they have declared types; that is,
    /// functions with inferred types are not considered part of a module's external API.
    /// This means we don't need to compute a project-wide inference order, which simplifies some things.
    fn compute_inference_order(&self, source: Source) -> Dr<Vec<Str>>;
    /// Compute values and types where possible.
    /// If a variable's type could not be deduced, or an error was encountered during type/value inference,
    /// an error will be returned.
    fn infer_values(&self, source: Source) -> Dr<Arc<ModuleParseResult<TypedInfos>>>;
}

/// A set of infos that may be useful to any feather compiler component.
/// This is an adapted version of the information contained in [`DefaultInfos`],
/// by including the known, semantically correct, types of each value.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct TypedInfos {
    pub expr_at: NodeInfoContainer<ExprContents, SourceSpan>,
    pub expr_ty: NodeInfoContainer<ExprContents, PartialExprTy>,
    pub name_at: NodeInfoContainer<Str, SourceSpan>,
}

#[tracing::instrument(level = "trace")]
fn def_deps(db: &dyn ValueInferenceEngine, source: Source) -> Dr<BTreeMap<Str, BTreeSet<Path>>> {
    db.module_from_feather_source(source).map(|res| {
        res.module
            .contents
            .defs
            .iter()
            .map(|def| {
                (def.contents.name.contents, {
                    let mut result = BTreeSet::new();
                    find_expr_def_deps(db, &def.contents.expr, &res.infos, &mut result);
                    debug!(
                        "def {} depends on [{}]",
                        db.lookup_intern_string_data(def.contents.name.contents),
                        result
                            .iter()
                            .map(|path| db.path_to_string(*path))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    result
                })
            })
            .collect()
    })
}

/// Work out which definitions this expression references.
/// For each `inst` expression, add it to the list of deps.
fn find_expr_def_deps(
    db: &dyn ValueInferenceEngine,
    expr: &Expr,
    infos: &DefaultInfos,
    deps: &mut BTreeSet<Path>,
) {
    match &expr.contents {
        ExprContents::Inst(inst) => {
            deps.insert(db.qualified_name_to_path(&inst.name));
        }
        _ => {
            for sub_expr in expr.contents.sub_expressions() {
                find_expr_def_deps(db, sub_expr, infos, deps);
            }
        }
    }
    if let Some(ExprTy(ty)) = infos.expr_ty.get(expr) {
        find_expr_def_deps(db, ty, infos, deps);
    }
}

#[tracing::instrument(level = "trace")]
fn local_def_deps(
    db: &dyn ValueInferenceEngine,
    source: Source,
) -> Dr<BTreeMap<Str, BTreeSet<Str>>> {
    db.def_deps(source).map(|map| {
        map.into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .filter_map(|path| {
                            // If this path represents a definition in this source file, keep it.
                            let (source_file_name, def_name) = db.split_path_last(path);
                            if source_file_name == source.path {
                                Some(def_name)
                            } else {
                                None
                            }
                        })
                        .collect(),
                )
            })
            .collect()
    })
}

#[tracing::instrument(level = "trace")]
fn compute_inference_order(db: &dyn ValueInferenceEngine, source: Source) -> Dr<Vec<Str>> {
    db.local_def_deps(source).bind(|mut deps| {
        debug!("deps are: {:#?}", deps);

        // Execute Kahn's topological sort algorithm to determine an inference order.
        // We say that if A has B as a dependency, there is an edge from B to A.
        // So `deps` is a map of incoming edges.
        // First, invert the `deps` map to find outgoing edges.
        let mut used_in = BTreeMap::<Str, BTreeSet<Str>>::new();
        for (def, def_deps) in &deps {
            for dep in def_deps {
                used_in.entry(*dep).or_default().insert(*def);
            }
        }

        debug!("used_in: {:#?}", used_in);

        let mut no_dependencies = deps
            .iter()
            .filter_map(|(k, v)| if v.is_empty() { Some(*k) } else { None })
            .collect::<Vec<_>>();

        // Remove any definitions without dependencies from the set of dependencies,
        // so that we don't see it later when checking for cycles.
        for e in &no_dependencies {
            deps.remove(e);
        }

        let mut result = Vec::new();
        while let Some(def) = no_dependencies.pop() {
            result.push(def);
            // For each function this one was used in...
            if let Some(used_in) = used_in.get(&def) {
                for dep in used_in {
                    // Remove this function from its dependency set.
                    let dependency_set = deps.get_mut(dep).unwrap();
                    dependency_set.remove(&def);
                    // Check if it has any more dependencies.
                    if dependency_set.is_empty() {
                        deps.remove(dep);
                        no_dependencies.push(*dep);
                    }
                }
            }
        }

        if !deps.is_empty() {
            // There was a cycle in the graph.
            todo!("report cycles: {:#?}", deps)
        }

        Dr::ok(result)
    })
}

#[tracing::instrument(level = "trace")]
fn infer_values(
    db: &dyn ValueInferenceEngine,
    source: Source,
) -> Dr<Arc<ModuleParseResult<TypedInfos>>> {
    db.compute_inference_order(source).bind(|order| {
        // We need to call `db.module_from_feather_source` a second time, even though we already did that in `compute_inference_order`.
        // Of course, due to `salsa`, we don't actually do the parse twice, but we need to be careful not to doubly-include diagnostics.
        let res = db
            .module_from_feather_source(source)
            .destructure()
            .0
            .unwrap();

        let mut result_types = Dr::ok(NodeInfoContainer::new());
        for def in order {
            // Update result_types with inferred information.
        }
        result_types.map(|final_types| {
            Arc::new(ModuleParseResult {
                module: Arc::clone(&res.module),
                node_id_gen: res.node_id_gen.clone(),
                infos: TypedInfos {
                    expr_at: res.infos.expr_at.clone(),
                    expr_ty: final_types,
                    name_at: res.infos.name_at.clone(),
                },
            })
        })
    })
}
