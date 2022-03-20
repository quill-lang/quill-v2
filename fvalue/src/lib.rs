//! Computes values of expressions and performs value inference.

mod value;
pub use value::*;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
};

use fcommon::{Dr, Label, LabelType, Path, Report, ReportKind, Source, Span, Str};
use fnodes::{
    basic_nodes::SourceSpan, expr::*, DefaultInfos, Definition, ModuleParseResult, NodeId,
    NodeInfoContainer, SexprParserExt,
};
use tracing::{debug, trace};

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
                    find_expr_def_deps(db, &def.contents.expr, &mut result);
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
fn find_expr_def_deps(db: &dyn ValueInferenceEngine, expr: &Expr, deps: &mut BTreeSet<Path>) {
    match &expr.contents {
        ExprContents::Inst(inst) => {
            deps.insert(db.qualified_name_to_path(&inst.0));
        }
        _ => {
            for sub_expr in expr.contents.sub_expressions() {
                find_expr_def_deps(db, sub_expr, deps);
            }
        }
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
            result_types = result_types.bind(|types_container| {
                infer_values_def(
                    db,
                    source,
                    res.module.definition(def).unwrap(),
                    &types_container,
                    &res.infos,
                )
                .deny()
                .map(|types| types_container.union(types))
            });
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

/// Infers types of each sub-expression in a given definition.
/// `known_local_types` is the set of types that we currently know about.
/// In particular, any locally-defined definitions (in this module) have known types listed in this map.
#[tracing::instrument(level = "trace")]
fn infer_values_def(
    db: &dyn ValueInferenceEngine,
    source: Source,
    def: &Definition,
    known_local_types: &NodeInfoContainer<ExprContents, PartialExprTy>,
    infos: &DefaultInfos,
) -> Dr<NodeInfoContainer<ExprContents, PartialExprTy>> {
    // To each expression we associate a type.
    // TODO: use tys from node info in `res`
    // TODO: variable ID generator should be initialised with non-clashing IDs from the expression, since it may have its own IDs already
    debug!("def was: {:#?}", def);
    let mut ctx = TyCtx {
        db,
        source,
        var_gen: Default::default(),
        known_local_types,
        print: PartialValuePrinter::new(db),
        infos,
    };
    let unification = traverse(&def.contents.expr, &mut ctx, &[]);
    let errored = unification.errored();
    unification.bind(|unif| {
        // Store the deduced type of each expression.
        let mut types = NodeInfoContainer::<ExprContents, PartialExprTy>::new();
        let result = fill_types(&mut ctx, &def.contents.expr, &unif, &mut types);
        debug!("types were: {:#?}", types);
        // Don't produce error messages for unknown types if we already have type inference errors.
        // We still want to produce the side effect of filling `types` though.
        if errored {
            Dr::ok(types)
        } else {
            result.map(|()| types)
        }
    })
}

/// Do not mutate any values in `TyCtx` except for `print`, which may be used mutably.
struct TyCtx<'a> {
    db: &'a dyn ValueInferenceEngine,
    source: Source,
    var_gen: VarGenerator,
    known_local_types: &'a NodeInfoContainer<ExprContents, PartialExprTy>,
    print: PartialValuePrinter<'a>,
    infos: &'a DefaultInfos,
}

/// Represents the types of known expressions and type variables at some stage in type inference.
/// Any methods that return a [`Vec<Label>`] are diagnostic methods; if they return a non-empty list,
/// the labels should be attached to a [`Report`] and encased in a [`Dr`].
#[derive(Debug, Default)]
struct Unification {
    expr_types: HashMap<NodeId, PartialValue>,
    /// A map converting a variable into a canonical representation.
    var_types: HashMap<Var, PartialValue>,
}

impl Unification {
    /// Construct a blank unification that contains only the information for a single expression.
    fn new_with_expr_type(expr: &Expr, ty: PartialValue) -> Self {
        let mut result = Self::default();
        result.insert_expr_type(expr, ty);
        result
    }

    /// Record the type of a single node.
    fn insert_expr_type(&mut self, expr: &Expr, ty: PartialValue) {
        self.insert_expr_type_from_id(expr.id(), ty)
    }

    /// Record the type of a single node.
    /// Call [`Self::insert_expr_type`] instead, if possible.
    fn insert_expr_type_from_id(&mut self, node_id: NodeId, mut ty: PartialValue) {
        self.canonicalise(&mut ty);
        self.expr_types.insert(node_id, ty);
    }

    /// Record the type of a single node.
    fn with_expr_type(mut self, expr: &Expr, ty: PartialValue) -> Self {
        self.insert_expr_type(expr, ty);
        self
    }

    /// Record the type of a single inference variable.
    /// If this causes an occurs check to fail, which can happen with circularly defined types,
    /// an error will be emitted.
    fn insert_var_type(
        &mut self,
        ctx: &mut TyCtx,
        span: Span,
        var: Var,
        mut ty: PartialValue,
    ) -> Vec<Label> {
        trace!("inferring {:?} -> {:?}", var, ty);
        // Run an occurs check on `ty` to see if the variable occurs in its replacement.
        if matches!(ty, PartialValue::Var(_)) {
            // Skip the occurs check, it's trivial anyway.
        } else if self.occurs_in(&var, &ty) {
            // TODO: Add node information, showing which nodes had this bad type.
            return vec![
                Label::new(ctx.source, span, LabelType::Error).with_message(format!(
                    "found self-referential type {} ~ {}",
                    ctx.print.print(&PartialValue::Var(var)),
                    ctx.print.print(&ty)
                )),
            ];
        }
        self.canonicalise(&mut ty);
        if let Some(previous_inference) = self.var_types.insert(var, ty) {
            panic!(
                "tried to set already-defined variable {:?} (was {:?})",
                var, previous_inference
            );
        }

        // TODO: We may want to canonicalise all the expr types we found that depend on this var,
        // although it's fine if that just happens ad hoc.
        Vec::new()
    }

    /// Returns true if the variable occurs in the given value.
    fn occurs_in(&self, var: &Var, val: &PartialValue) -> bool {
        match val {
            PartialValue::Var(var2) => var == var2,
            _ => val
                .sub_values()
                .iter()
                .any(|expr| self.occurs_in(var, expr)),
        }
    }

    /// Returns the names of any inference variables that occur in the given value.
    fn variables_occuring_in(&self, val: &PartialValue) -> HashSet<Var> {
        match val {
            PartialValue::Var(var) => {
                let mut result = HashSet::new();
                result.insert(*var);
                result
            }
            _ => val
                .sub_values()
                .iter()
                .flat_map(|expr| self.variables_occuring_in(expr))
                .collect(),
        }
    }

    /// Assuming that there are no duplicates, return the union of the two unifications.
    // TODO: This assumption isn't actually necessarily true...?
    fn with(mut self, other: Self, ctx: &mut TyCtx, span: Span) -> Dr<Self> {
        let mut labels = Vec::new();
        for (var, ty) in other.var_types {
            labels.extend(self.insert_var_type(ctx, span.clone(), var, ty));
        }
        for (node_id, mut val) in other.expr_types {
            self.canonicalise(&mut val);
            self.insert_expr_type_from_id(node_id, val);
        }
        if labels.is_empty() {
            Dr::ok(self)
        } else {
            todo!()
        }
    }

    /// An idempotent operation reducing a value to a standard form.
    fn canonicalise(&self, val: &mut PartialValue) {
        match val {
            PartialValue::Var(var) => match self.var_types.get(var) {
                // TODO: Is this operation really idempotent?
                Some(PartialValue::Var(var2)) => *var = *var2,
                Some(value) => {
                    *val = value.clone();
                    self.canonicalise(val);
                }
                None => {}
            },
            PartialValue::FormProduct(FormProduct { fields }) => {
                for field in fields {
                    self.canonicalise(&mut field.ty);
                }
            }
            _ => {
                for expr in val.sub_values_mut() {
                    self.canonicalise(expr);
                }
            }
        }
    }

    /// Unify the two partial values.
    /// If an error was found, the `report` function is called, which should generate a suitable report.
    /// The arguments are the canonicalised versions of `expected` and `found`.
    fn unify<R>(
        mut self,
        mut expected: PartialValue,
        mut found: PartialValue,
        ctx: &mut TyCtx,
        span: Span,
        report: R,
    ) -> Dr<Self>
    where
        R: FnOnce(&mut TyCtx, &PartialValue, &PartialValue) -> Report,
    {
        // Recall everything we currently know about the two values we're dealing with.
        self.canonicalise(&mut expected);
        self.canonicalise(&mut found);

        trace!("unifying {:?}, {:?}", expected, found);

        // The report should only be called once, but it's easier to implement without this compile time restriction.
        // So we put it in an Option, and take it out when we need it.
        let labels = self.unify_recursive(ctx, span, &expected, &found);
        if labels.is_empty() {
            Dr::ok(self)
        } else {
            Dr::ok_with(
                self,
                labels
                    .into_iter()
                    .fold(report(ctx, &expected, &found), |report, label| {
                        report.with_label(label)
                    }),
            )
        }
    }

    /// Do not call this manually.
    /// Given canonicalised types, unify them.
    /// If the unification could not occur, the report is emitted using `base_expected` and `base_found`.
    /// Returns a list of labels which detail type errors. If no labels were emitted, this operation succeeded.
    fn unify_recursive(
        &mut self,
        ctx: &mut TyCtx,
        span: Span,
        expected: &PartialValue,
        found: &PartialValue,
    ) -> Vec<Label> {
        match (expected, found) {
            (
                PartialValue::FormFunc(FormFunc {
                    parameter: expected_parameter,
                    result: expected_result,
                }),
                PartialValue::FormFunc(FormFunc {
                    parameter: found_parameter,
                    result: found_result,
                }),
            ) => {
                // Unify the parameters and then the results.
                let mut labels =
                    self.unify_recursive(ctx, span.clone(), expected_parameter, found_parameter);

                // At this point, the canonical form of the result may have changed.
                // So we need to recanonicalise it.
                let mut expected_result = *expected_result.clone();
                let mut found_result = *found_result.clone();
                self.canonicalise(&mut expected_result);
                self.canonicalise(&mut found_result);
                labels.extend(self.unify_recursive(ctx, span, &expected_result, &found_result));

                labels
            }
            (
                PartialValue::FormProduct(FormProduct {
                    fields: expected_fields,
                }),
                PartialValue::FormProduct(FormProduct {
                    fields: found_fields,
                }),
            ) => {
                // TODO: Enhance this check to work out if there were missing or mistyped fields.
                if expected_fields.len() != found_fields.len() {
                    vec![Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(
                            format!(
                                "product types {} and {} had differing amounts of fields, so could not be compared",
                                ctx.print.print(expected),
                                ctx.print.print(found)
                            )
                        )]
                } else {
                    let mut labels = Vec::new();
                    for (expected, found) in expected_fields.iter().zip(found_fields) {
                        // At this point, the canonical form of the result may have changed.
                        // So we need to recanonicalise it.
                        let mut expected_ty = expected.ty.clone();
                        let mut found_ty = found.ty.clone();
                        self.canonicalise(&mut expected_ty);
                        self.canonicalise(&mut found_ty);
                        labels.extend(self.unify_recursive(
                            ctx,
                            span.clone(),
                            &expected_ty,
                            &found_ty,
                        ));
                    }
                    labels
                }
            }
            (other, PartialValue::Var(var)) | (PartialValue::Var(var), other) => {
                // Since we've canonicalised `var`, self.var_types.get(&var) is either None or Some(var).
                // We will replace this entry with `other`.
                self.insert_var_type(ctx, span, *var, other.clone())
            }
            _ => {
                // Directly test for equality.
                if expected == found {
                    Vec::new()
                } else {
                    // We couldn't unify the two types.
                    vec![
                        Label::new(ctx.source, span, LabelType::Note).with_message(format!(
                            "types {} and {} could not be unified",
                            ctx.print.print(expected),
                            ctx.print.print(found),
                        )),
                    ]
                }
            }
        }
    }

    fn expr_type(&self, expr: &Expr) -> PartialValue {
        let mut result = self.expr_types[&expr.id()].clone();
        self.canonicalise(&mut result);
        result
    }
}

/// Traverses the expression syntax tree, working out the *types* of each expression.
/// Once types are known, we can call [`evaluate`] to compute the value of each expression.
///
/// `locals` is the list of the types associated with each local.
/// The de Bruijn index `n` refers to the `n`th entry in this slice.
fn traverse(expr: &Expr, ctx: &mut TyCtx, locals: &[PartialValue]) -> Dr<Unification> {
    traverse_inner(expr, ctx, locals).bind(|unif| {
        // Once we've done type inference for this expression, unify it with the stated type.
        if let Some(ExprTy(stated_type)) = ctx.infos.expr_ty.get(expr) {
            debug!("found stated type {:#?} for {:#?}", stated_type, expr);
            traverse(stated_type, ctx, locals)
                .bind(|inner_unif| unif.with(inner_unif, ctx, stated_type.span()))
                .bind(|unif| {
                    evaluate(stated_type, ctx, &unif).bind(|stated_type_evaluated| {
                        let found_type = unif.expr_type(expr);
                        unif.unify(
                            stated_type_evaluated,
                            found_type,
                            ctx,
                            stated_type.span(),
                            |ctx, expected, found| {
                                Report::new(ReportKind::Error, ctx.source, stated_type.span().start)
                                    .with_message("stated type did not match expression type")
                                    .with_label(
                                        Label::new(ctx.source, expr.span(), LabelType::Error)
                                            .with_message(format!(
                                                "this expression has type {}",
                                                ctx.print.print(found)
                                            )),
                                    )
                                    .with_label(
                                        Label::new(
                                            ctx.source,
                                            stated_type.span(),
                                            LabelType::Error,
                                        )
                                        .with_message(
                                            format!(
                                                "the expected type of the expression was {}",
                                                ctx.print.print(expected)
                                            ),
                                        ),
                                    )
                            },
                        )
                    })
                })
        } else {
            Dr::ok(unif)
        }
    })
}

/// Do not call manually - use `traverse` instead.
/// This function essentially codifies the type behaviour of each expression type.
///
/// `locals` is the list of the types associated with each local.
/// The de Bruijn index `n` refers to the `n`th entry in this slice.
fn traverse_inner(expr: &Expr, ctx: &mut TyCtx, locals: &[PartialValue]) -> Dr<Unification> {
    debug!("traversing {:#?}", expr);
    // TODO: Raise errors if a de Bruijn index was too high instead of panicking.
    match &expr.contents {
        ExprContents::IntroLocal(IntroLocal(n)) => Dr::ok(Unification::new_with_expr_type(
            expr,
            locals[n.0 as usize].clone(),
        )),
        ExprContents::IntroU64(_) => {
            Dr::ok(Unification::new_with_expr_type(expr, PartialValue::FormU64))
        }
        ExprContents::IntroFalse => todo!(),
        ExprContents::IntroTrue => todo!(),
        ExprContents::IntroUnit => Dr::ok(Unification::new_with_expr_type(
            expr,
            PartialValue::FormUnit,
        )),
        ExprContents::FormU64 | ExprContents::FormBool | ExprContents::FormUnit => Dr::ok(
            Unification::new_with_expr_type(expr, PartialValue::FormUniverse),
        ),
        ExprContents::IntroProduct(IntroProduct { fields }) => {
            // Traverse each field.
            fields
                .iter()
                .fold(Dr::ok(Unification::default()), |unif, field| {
                    unif.bind(|unif| {
                        traverse(&field.expr, ctx, locals)
                            .bind(|unif2| unif.with(unif2, ctx, expr.span()))
                    })
                })
                .map(|unif| {
                    let expr_ty = PartialValue::FormProduct(FormProduct {
                        fields: fields
                            .iter()
                            .map(|component| ComponentContents {
                                name: component.name.contents,
                                ty: unif.expr_type(&component.expr),
                            })
                            .collect(),
                    });
                    unif.with_expr_type(expr, expr_ty)
                })
        }
        ExprContents::FormProduct(FormProduct { fields }) => {
            // Traverse each field.
            fields
                .iter()
                .fold(Dr::ok(Unification::default()), |unif, field| {
                    unif.bind(|unif| {
                        traverse(&field.contents.ty, ctx, locals)
                            .bind(|unif2| unif.with(unif2, ctx, expr.span()))
                    })
                })
                .map(|unif| unif.with_expr_type(expr, PartialValue::FormUniverse))
        }
        ExprContents::MatchProduct(MatchProduct {
            fields,
            product,
            body,
        }) => {
            // Traverse the product type itself and then the body.
            traverse(product, ctx, locals).bind(|unif| {
                // Construct new inference variables for the field types of the product.
                let field_types = fields.iter().map(|_| ctx.var_gen.gen()).collect::<Vec<_>>();
                let expected_product_type = PartialValue::FormProduct(FormProduct {
                    fields: fields
                        .iter()
                        .zip(&field_types)
                        .map(|(name, var)| ComponentContents {
                            name: name.contents,
                            ty: PartialValue::Var(*var),
                        })
                        .collect(),
                });

                // Unify `product` with this new product type.
                let product_type = unif.expr_type(product);
                unif.unify(
                    expected_product_type,
                    product_type,
                    ctx,
                    expr.span(),
                    |_ctx, _expected, _found| {
                        todo!("tried to invoke `mprod` on a non-product type")
                    },
                )
                .bind(|unif| {
                    // Add the result of this inference to the list of locals.
                    let internal_locals = field_types
                        .iter()
                        .rev()
                        .map(|v| {
                            let mut ty = PartialValue::Var(*v);
                            unif.canonicalise(&mut ty);
                            ty
                        })
                        .chain(locals.iter().cloned())
                        .collect::<Vec<_>>();
                    traverse(body, ctx, &internal_locals)
                        .bind(|body_unif| body_unif.with(unif, ctx, expr.span()))
                        .map(|unif| {
                            // The type of a match expression is the type of its body.
                            let result_ty = unif.expr_type(body);
                            unif.with_expr_type(expr, result_ty)
                        })
                })
            })
        }
        ExprContents::Inst(Inst(qualified_name)) => {
            let (source_file, def_name) = ctx
                .db
                .split_path_last(ctx.db.qualified_name_to_path(qualified_name));
            if source_file == ctx.source.path {
                // This is a local definition.
                // So its type should be present in `ctx.known_local_types`.
                let ty = ctx
                    .known_local_types
                    .get(
                        &ctx.db
                            .module_from_feather_source(ctx.source)
                            .destructure()
                            .0
                            .unwrap()
                            .module
                            .definition(def_name)
                            .unwrap()
                            .contents
                            .expr,
                    )
                    .unwrap();
                Dr::ok(Unification::new_with_expr_type(expr, ty.0.clone()))
            } else {
                // This is a definition we've imported from somewhere else.
                // So we need to look into the database for its type.
                todo!()
            }
        }
        ExprContents::Let(Let { to_assign, body }) => {
            // Traverse the expression to assign to a new variable first.
            traverse(to_assign, ctx, locals).bind(|to_assign_unif| {
                // Add the result of this inference to the list of locals.
                let internal_locals = std::iter::once(to_assign_unif.expr_type(to_assign))
                    .chain(locals.iter().cloned())
                    .collect::<Vec<_>>();
                // Traverse the body.
                traverse(body, ctx, &internal_locals).bind(|inner_unif| {
                    // The type of a let expression is the type of its body.
                    let result_ty = inner_unif.expr_type(body);
                    inner_unif
                        .with(to_assign_unif, ctx, expr.span())
                        .map(|unif| unif.with_expr_type(expr, result_ty))
                })
            })
        }
        ExprContents::Lambda(Lambda {
            binding_count,
            body,
        }) => {
            // Construct new type variables for these locals.
            let new_locals = (0..*binding_count)
                .into_iter()
                .map(|_| PartialValue::Var(ctx.var_gen.gen()))
                .collect::<Vec<_>>();
            // Construct the list of locals as seen from inside the lambda itself.
            let internal_locals = new_locals
                .iter()
                .rev()
                .chain(locals.iter())
                .cloned()
                .collect::<Vec<_>>();
            // Traverse the body and do an inner step of type inference.
            traverse(body, ctx, &internal_locals).map(|body_unif| {
                // Construct the result type of this abstraction.
                // For each local, add it as a parameter to the function's type.
                let func_ty = new_locals.into_iter().rev().fold(
                    body_unif.expr_type(body),
                    |result, parameter| {
                        PartialValue::FormFunc(FormFunc {
                            parameter: Box::new(parameter),
                            result: Box::new(result),
                        })
                    },
                );
                body_unif.with_expr_type(expr, func_ty)
            })
        }
        ExprContents::Apply(Apply { function, argument }) => {
            // Traverse the function's body.
            traverse(function, ctx, locals).bind(|unif| {
                // Construct a new inference variable for the result type.
                let result_ty = ctx.var_gen.gen();
                let function_type = unif.expr_type(function);
                let found_type = PartialValue::FormFunc(FormFunc {
                    parameter: Box::new(locals[argument.0 as usize].clone()),
                    result: Box::new(PartialValue::Var(result_ty)),
                });
                unif.unify(
                    function_type,
                    found_type,
                    ctx,
                    expr.span(),
                    |ctx, expected, found| {
                        Report::new(ReportKind::Error, ctx.source, expr.span().start)
                            .with_message("type mismatch when calling function")
                            .with_label(
                                Label::new(ctx.source, function.span(), LabelType::Error)
                                    .with_message(format!(
                                        "the function had type {}",
                                        ctx.print.print(expected)
                                    ))
                                    .with_order(0),
                            )
                            .with_label(
                                if let PartialValue::FormFunc(FormFunc { parameter, .. }) = found {
                                    Label::new(ctx.source, function.span(), LabelType::Error)
                                        .with_message(format!(
                                            "the argument had type {}",
                                            ctx.print.print(parameter)
                                        ))
                                        .with_order(10)
                                } else {
                                    panic!()
                                },
                            )
                    },
                )
                .map(|unif| unif.with_expr_type(expr, PartialValue::Var(result_ty)))
            })
        }
        ExprContents::Var(_) => todo!(),
        ExprContents::FormFunc(FormFunc { parameter, result }) => traverse(parameter, ctx, locals)
            .bind(|unif| {
                traverse(result, ctx, locals).bind(|unif2| unif.with(unif2, ctx, expr.span()))
            })
            .map(|unif| unif.with_expr_type(expr, PartialValue::FormUniverse)),
        ExprContents::FormUniverse => Dr::ok(Unification::new_with_expr_type(
            expr,
            PartialValue::FormUniverse,
        )),
    }
}

fn fill_types(
    ctx: &mut TyCtx,
    expr: &Expr,
    unif: &Unification,
    types: &mut NodeInfoContainer<ExprContents, PartialExprTy>,
) -> Dr<()> {
    let ty = unif.expr_type(expr);

    let vars_occuring = unif.variables_occuring_in(&ty);

    let result = if !vars_occuring.is_empty() {
        Dr::ok_with(
            (),
            Report::new(ReportKind::Error, ctx.source, expr.span().start)
                .with_message("could not deduce type")
                .with_label(
                    Label::new(ctx.source, expr.span(), LabelType::Error)
                        .with_message(format!("deduced type {}", ctx.print.print(&ty))),
                ),
        )
    } else {
        types.insert(expr, PartialExprTy(ty));
        Dr::ok(())
    };

    result.bind(|()| {
        // For each sub-expression, fill the types container.
        expr.contents
            .sub_expressions()
            .iter()
            .fold(Dr::ok(()), |result, sub_expr| {
                result.bind(|()| fill_types(ctx, sub_expr, unif, types))
            })
    })
}

/// Try to evaluate this expression, given its type.
fn evaluate(expr: &Expr, ctx: &mut TyCtx, unif: &Unification) -> Dr<PartialValue> {
    match &expr.contents {
        ExprContents::IntroLocal(_) => todo!(),
        ExprContents::IntroU64(_) => todo!(),
        ExprContents::IntroFalse => todo!(),
        ExprContents::IntroTrue => todo!(),
        ExprContents::IntroUnit => todo!(),
        ExprContents::FormU64 => Dr::ok(PartialValue::FormU64),
        ExprContents::FormBool => todo!(),
        ExprContents::FormUnit => Dr::ok(PartialValue::FormUnit),
        ExprContents::IntroProduct(_) => todo!(),
        ExprContents::FormProduct(FormProduct { fields }) => {
            Dr::sequence(fields.iter().map(|field| {
                evaluate(&field.contents.ty, ctx, unif).map(|ty| ComponentContents {
                    name: field.contents.name.contents,
                    ty,
                })
            }))
            .map(|fields| PartialValue::FormProduct(FormProduct { fields }))
        }
        ExprContents::MatchProduct(_) => todo!(),
        ExprContents::Inst(_) => todo!(),
        ExprContents::Let(_) => todo!(),
        ExprContents::Lambda(_) => todo!(),
        ExprContents::Apply(_) => todo!(),
        ExprContents::Var(_) => todo!(),
        ExprContents::FormFunc(FormFunc { parameter, result }) => evaluate(parameter, ctx, unif)
            .bind(|parameter| {
                evaluate(result, ctx, unif).map(|result| {
                    PartialValue::FormFunc(FormFunc {
                        parameter: Box::new(parameter),
                        result: Box::new(result),
                    })
                })
            }),
        ExprContents::FormUniverse => todo!(),
    }
}
