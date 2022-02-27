//! Computes values of expressions and performs value inference.

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use fcommon::{Dr, Label, LabelType, Path, Report, ReportKind, Source};
use fnodes::{
    basic_nodes::SourceSpan, expr::*, NodeId, NodeIdGenerator, NodeInfoContainer, SexprParser,
};
use tracing::{debug, info};

#[salsa::query_group(ValueInferenceStorage)]
pub trait ValueInferenceEngine: SexprParser {
    fn infer_values(&self, source: Source) -> Dr<()>;
}

#[tracing::instrument(level = "trace")]
pub fn infer_values(db: &dyn ValueInferenceEngine, source: Source) -> Dr<()> {
    db.expr_from_feather_source(source).bind(|res| {
        // To each expression we associate a type.
        // TODO: use tys from node info in `res`
        // TODO: node ID generator should be initialised with non-clashing IDs from the expression, since it may have its own IDs already
        info!("{:#?}", res.expr);
        let mut tys = NodeInfoContainer::<ExprContents, Expr>::new();
        // Since we're parsing feather code not quill code, we need to fake the info for spans.
        // Normally, in a real quill program, we'd have `(at ...)` tags to give us span information.
        // But here, we need to fill this info in ourselves with the spans in the S-expression itself.
        let mut spans = NodeInfoContainer::<ExprContents, SourceSpan>::new();
        let mut constraints = Vec::new();
        let mut node_id_gen = res.node_id_gen.clone();
        let mut var_gen = VarGenerator::default();
        traverse(
            &res.expr,
            &mut tys,
            &mut spans,
            &[],
            &mut constraints,
            &mut node_id_gen,
            &mut var_gen,
        );
        debug!("tys:\n{:#?}", tys);
        debug!("constraints:\n{:#?}", constraints);
        let mut values = values(&res.expr, &tys);
        debug!("values:\n{:#?}", values);
        let connected_components = partition(&values, &constraints);
        debug!("connected components:\n{:#?}", connected_components);

        let mut var_to_val = HashMap::new();
        let mut reports = Vec::new();
        let mut components_with_representatives = Vec::new();
        for component in connected_components {
            let (rep, more_reports) =
                find_representative(source, &spans, &values, &component).destructure();
            reports.extend(more_reports);
            if let Some(rep) = rep.cloned() {
                debug!("rep:\n{:#?}\nfor {:#?}", rep, component);
                for &id in &component {
                    if let Some(PartialValue::Var(var)) = values.get_from_id(id) {
                        var_to_val.insert(*var, rep.clone());
                    }
                }
                components_with_representatives.push((component, rep));
            }
        }

        debug!("vars:\n{:#?}", var_to_val);
        for (component, mut representative) in components_with_representatives {
            representative.replace_vars(&var_to_val);
            for id in component {
                values.insert_from_id(id, representative.clone());
            }
        }
        debug!("result values:\n{:#?}", values);

        Dr::ok_with_many((), reports)
    })
}

#[derive(Debug)]
enum Constraint {
    Equality(Equality),
}

/// A constraint that two expressions evaluate to the same value.
#[derive(Debug)]
struct Equality {
    left: NodeId,
    right: NodeId,
}

/// `locals` is a stack of the locals in scope.
/// They can be indexed with de Bruijn indices.
fn traverse(
    expr: &Expr,
    tys: &mut NodeInfoContainer<ExprContents, Expr>,
    spans: &mut NodeInfoContainer<ExprContents, SourceSpan>,
    locals: &[NodeId],
    constraints: &mut Vec<Constraint>,
    node_id_gen: &mut NodeIdGenerator,
    var_gen: &mut VarGenerator,
) {
    spans.insert(expr, SourceSpan(expr.span()));
    let ty = match &expr.contents {
        ExprContents::IntroUnit(_) => Expr::new(
            node_id_gen.gen(),
            expr.span(),
            ExprContents::FormUnit(FormUnit),
        ),
        ExprContents::Lambda(lambda) => {
            // lambda (x0:T0) (x1:T1) ... (x(binding_count - 1):T(binding_count - 1))
            let (params, param_tys): (Vec<_>, Vec<_>) = (0..lambda.binding_count)
                .map(|_| {
                    // TODO: the parameter type should be spanned at the correct location, not the whole lambda
                    let param_val = Expr::new(
                        node_id_gen.gen(),
                        expr.span(),
                        ExprContents::Var(var_gen.gen()),
                    );
                    let param_ty = Expr::new(
                        node_id_gen.gen(),
                        expr.span(),
                        ExprContents::Var(var_gen.gen()),
                    );
                    spans.insert(&param_val, SourceSpan(expr.span()));
                    spans.insert(&param_ty, SourceSpan(expr.span()));
                    let ty_id = param_ty.id();
                    tys.insert(&param_val, param_ty);
                    (param_val, ty_id)
                })
                .unzip();

            info!("{:?}, {:?}", params, param_tys);

            // The last bound variable has the lowest de Bruijn index.
            let new_locals = params
                .iter()
                .rev()
                .map(|expr| expr.id())
                .chain(locals.iter().copied())
                .collect::<Vec<_>>();

            traverse(
                &lambda.body,
                tys,
                spans,
                &new_locals,
                constraints,
                node_id_gen,
                var_gen,
            );

            let mut result_ty = Expr::new(
                node_id_gen.gen(),
                expr.span(),
                ExprContents::Var(var_gen.gen()),
            );

            constraints.push(Constraint::Equality(Equality {
                left: tys.get(&lambda.body).unwrap().id(),
                right: result_ty.id(),
            }));

            for param_ty in param_tys.into_iter().rev() {
                spans.insert(&result_ty, SourceSpan(expr.span()));

                let param_ty_var = Expr::new(
                    node_id_gen.gen(),
                    expr.span(),
                    ExprContents::Var(var_gen.gen()),
                );
                spans.insert(&param_ty_var, SourceSpan(expr.span()));

                constraints.push(Constraint::Equality(Equality {
                    left: param_ty,
                    right: param_ty_var.id(),
                }));

                result_ty = Expr::new(
                    node_id_gen.gen(),
                    expr.span(),
                    ExprContents::FormFunc(FormFunc {
                        parameter: Box::new(param_ty_var),
                        result: Box::new(result_ty),
                    }),
                );
            }

            result_ty
        }
        ExprContents::Let(let_expr) => {
            traverse(
                &let_expr.to_assign,
                tys,
                spans,
                locals,
                constraints,
                node_id_gen,
                var_gen,
            );

            let new_locals = std::iter::once(let_expr.to_assign.id())
                .chain(locals.iter().copied())
                .collect::<Vec<_>>();

            traverse(
                &let_expr.body,
                tys,
                spans,
                &new_locals,
                constraints,
                node_id_gen,
                var_gen,
            );

            let result_ty = Expr::new(
                node_id_gen.gen(),
                expr.span(),
                ExprContents::Var(var_gen.gen()),
            );

            constraints.push(Constraint::Equality(Equality {
                left: tys.get(&let_expr.body).unwrap().id(),
                right: result_ty.id(),
            }));

            result_ty
        }
        ExprContents::IntroLocal(local) => {
            let result_ty = Expr::new(
                node_id_gen.gen(),
                expr.span(),
                ExprContents::Var(var_gen.gen()),
            );
            constraints.push(Constraint::Equality(Equality {
                left: tys.get_from_id(locals[local.0 .0 as usize]).unwrap().id(),
                right: result_ty.id(),
            }));
            result_ty
        }
        _ => todo!(),
    };
    spans.insert(&ty, SourceSpan(expr.span()));
    tys.insert(expr, ty);
}

/// Partition the set of nodes into equivalence classes given by the constraints.
/// Every node contained in `values` will be given an equivalence class.
fn partition(
    values: &NodeInfoContainer<ExprContents, PartialValue>,
    constraints: &[Constraint],
) -> Vec<HashSet<NodeId>> {
    // We perform a search for each connected component of the equality constraint graph.
    // This partitions types/values into equivalence classes.
    // For the moment, we ignore judgement constraints.
    let equality = constraints
        .iter()
        .map(|constraint| match constraint {
            Constraint::Equality(eq) => eq,
        })
        .collect::<Vec<_>>();

    // For each equality constraint (A = B), we add B to the list of neighbours of A, and vice versa.
    let mut adjacency_list = HashMap::<NodeId, HashSet<NodeId>>::new();
    for constraint in &equality {
        adjacency_list
            .entry(constraint.left)
            .or_default()
            .insert(constraint.right);
        adjacency_list
            .entry(constraint.right)
            .or_default()
            .insert(constraint.left);
    }

    let mut unsolved_ids = values.keys().copied().collect::<HashSet<_>>();
    debug!("ids: {:?}", unsolved_ids);

    // Now, perform a search on the graph represented by the adjacency list to find its connected components.
    let mut connected_components = Vec::new();
    while let Some(&unsolved_id) = unsolved_ids.iter().next() {
        // We still have unsolved IDs to unify.
        let mut component = HashSet::new();
        find_connected_component(&adjacency_list, unsolved_id, &mut component);
        // Remove the new component from the set of unsolved IDs.
        unsolved_ids.retain(|id| !component.contains(id));
        connected_components.push(component);
    }

    connected_components
}

/// Given an adjacency list for a graph, find the smallest connected component containing `value`.
/// The result is stored in `component`, which is assumed to be empty before calling the function.
fn find_connected_component<T>(
    adjacency_list: &HashMap<T, HashSet<T>>,
    value: T,
    component: &mut HashSet<T>,
) where
    T: Eq + Hash + Clone,
{
    // The component naturally contains the given value.
    component.insert(value.clone());
    // It also contains every connected component of everything adjacent to it.
    if let Some(neighbours) = adjacency_list.get(&value) {
        for neighbour in neighbours {
            if !component.contains(neighbour) {
                find_connected_component(adjacency_list, neighbour.clone(), component);
            }
            // If we already contain this neighbour, there's no point traversing the tree again.
        }
    }
}

/// A realisation of an object which may contain inference variables, and may be simplifiable.
/// Importantly, it contains no provenance about where it came from in the expression - all we care
/// about is its value.
/// It therefore contains no feather nodes, and is cloneable.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PartialValue {
    IntroLocal(IntroLocal),

    IntroU64(IntroU64),
    IntroFalse,
    IntroTrue,
    IntroUnit,

    FormU64,
    FormBool,
    FormUnit,

    Inst(Path),
    Let(Let<PartialValue>),
    Lambda(Lambda<PartialValue>),
    Apply(Apply<PartialValue>),
    Var(Var),

    FormFunc(FormFunc<PartialValue>),
}

impl PartialValue {
    /// Replace all instances of inference variables with their values.
    fn replace_vars(&mut self, var_to_val: &HashMap<Var, PartialValue>) {
        match self {
            PartialValue::Let(Let { to_assign, body }) => {
                to_assign.replace_vars(var_to_val);
                body.replace_vars(var_to_val);
            }
            PartialValue::Lambda(Lambda { body, .. }) => {
                body.replace_vars(var_to_val);
            }
            PartialValue::Apply(_) => todo!(),
            PartialValue::Var(var) => {
                if let Some(val) = var_to_val.get(var) {
                    *self = val.clone();
                }
            }
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                parameter.replace_vars(var_to_val);
                result.replace_vars(var_to_val);
            }
            _ => {}
        }
    }
}

/// Computes values for each expression and type in the list of expressions and types provided, if possible.
fn values(
    expr: &Expr,
    tys: &NodeInfoContainer<ExprContents, Expr>,
) -> NodeInfoContainer<ExprContents, PartialValue> {
    let mut container = NodeInfoContainer::new();
    compute_values_of_expr(expr, &mut container);
    for (_id, ty_expr) in tys.iter() {
        compute_values_of_expr(ty_expr, &mut container);
    }
    container
}

/// Converts this expression into a partial value and emplaces it in the given container.
fn compute_values_of_expr(
    expr: &Expr,
    container: &mut NodeInfoContainer<ExprContents, PartialValue>,
) -> PartialValue {
    let result = match &expr.contents {
        ExprContents::IntroLocal(local) => PartialValue::IntroLocal(*local),
        ExprContents::IntroU64(val) => PartialValue::IntroU64(*val),
        ExprContents::IntroFalse(_) => todo!(),
        ExprContents::IntroTrue(_) => todo!(),
        ExprContents::IntroUnit(_) => PartialValue::IntroUnit,
        ExprContents::FormU64(_) => todo!(),
        ExprContents::FormBool(_) => todo!(),
        ExprContents::FormUnit(_) => PartialValue::FormUnit,
        ExprContents::Inst(_) => todo!(),
        ExprContents::Let(Let { to_assign, body }) => PartialValue::Let(Let {
            to_assign: Box::new(compute_values_of_expr(to_assign, container)),
            body: Box::new(compute_values_of_expr(body, container)),
        }),
        ExprContents::Lambda(Lambda {
            binding_count,
            body,
        }) => PartialValue::Lambda(Lambda {
            binding_count: *binding_count,
            body: Box::new(compute_values_of_expr(body, container)),
        }),
        ExprContents::Apply(_) => todo!(),
        ExprContents::Var(var) => PartialValue::Var(*var),
        ExprContents::FormFunc(FormFunc { parameter, result }) => {
            PartialValue::FormFunc(FormFunc {
                parameter: Box::new(compute_values_of_expr(parameter, container)),
                result: Box::new(compute_values_of_expr(result, container)),
            })
        }
    };
    container.insert(expr, result.clone());
    result
}

/// Find the most general unifier of all elements in this connected component of the constraint graph.
/// This entails finding equivalences of expressions, so we need to have evaluated expressions as partial values.
fn find_representative<'a>(
    source: Source,
    spans: &NodeInfoContainer<ExprContents, SourceSpan>,
    values: &'a NodeInfoContainer<ExprContents, PartialValue>,
    component: &HashSet<NodeId>,
) -> Dr<&'a PartialValue> {
    // If any of the elements is an inference variable, it can be excluded from the search for a representative.
    let (var_types, representative_candidates): (Vec<NodeId>, Vec<NodeId>) = component
        .iter()
        .partition(|&&id| matches!(values.get_from_id(id).unwrap(), PartialValue::Var(_)));
    // All remaining representative candidates must now have values which match exactly, and this list must be non-empty.
    if let Some(&representative) = representative_candidates.get(0) {
        let representative_ty = values.get_from_id(representative).unwrap();
        for &other in &representative_candidates[1..] {
            if representative_ty != values.get_from_id(other).unwrap() {
                panic!("mismatch");
            }
        }
        Dr::ok(representative_ty)
    } else {
        let mut var_spans = var_types
            .iter()
            .map(|id| spans.get_from_id(*id).unwrap())
            .collect::<Vec<_>>();
        var_spans.sort();
        let mut reports = Vec::new();
        for span in var_spans {
            let report = Report::new(ReportKind::Error, source, span.0.start)
                .with_message("could not deduce the type of this expression")
                .with_label(Label::new(source, span.0.clone(), LabelType::Error));
            reports.push(report);
        }
        Dr::fail_many(reports)
    }
}
