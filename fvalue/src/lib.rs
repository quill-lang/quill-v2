//! Computes values of expressions and performs value inference.

mod value;
pub use value::*;

use std::collections::HashMap;

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, Span};
use fnodes::{expr::*, NodeId, SexprParser};
use tracing::info;

#[salsa::query_group(ValueInferenceStorage)]
pub trait ValueInferenceEngine: SexprParser {
    fn infer_values(&self, source: Source) -> Dr<()>;
}

#[tracing::instrument(level = "trace")]
pub fn infer_values(db: &dyn ValueInferenceEngine, source: Source) -> Dr<()> {
    db.expr_from_feather_source(source).bind(|res| {
        // To each expression we associate a type.
        // TODO: use tys from node info in `res`
        // TODO: variable ID generator should be initialised with non-clashing IDs from the expression, since it may have its own IDs already
        info!("{:#?}", res.expr);
        let mut ctx = TyCtx {
            db,
            source,
            var_gen: Default::default(),
        };
        traverse(&res.expr, &mut ctx, &[]).map(|unif| info!("{:#?}", unif))
    })
}

struct TyCtx<'a> {
    db: &'a dyn ValueInferenceEngine,
    source: Source,
    var_gen: VarGenerator,
}

/// Represents the types of known expressions and type variables at some stage in type inference.
#[derive(Debug, Default)]
struct Unification {
    expr_types: HashMap<NodeId, PartialValue>,
    /// A map converting a variable into a canonical representation.
    var_types: HashMap<Var, PartialValue>,
}

impl Unification {
    /// Construct a blank unification that contains only the information for a single expression.
    fn new_with_expr_type(node_id: NodeId, ty: PartialValue) -> Self {
        Self::default().with_expr_type(node_id, ty)
    }

    /// Record the type of a single node.
    fn with_expr_type(mut self, node_id: NodeId, mut ty: PartialValue) -> Self {
        self.canonicalise(&mut ty);
        self.expr_types.insert(node_id, ty);
        self
    }

    /// Record the type of a single inference variable.
    /// If this causes an occurs check to fail, which can happen with circularly defined types,
    /// an error will be emitted.
    fn with_var_type(
        mut self,
        source: Source,
        span: Span,
        var: Var,
        mut ty: PartialValue,
    ) -> Dr<Self> {
        // Run an occurs check on `ty` to see if the variable occurs in its replacement.
        if matches!(ty, PartialValue::Var(_)) {
            // Skip the occurs check, it's trivial anyway.
        } else if self.occurs_in(&var, &ty) {
            // TODO: Add node information, showing which nodes had this bad type.
            return Dr::ok_with(
                self,
                Report::new(ReportKind::Error, source, span.start)
                    .with_message("self-referential type found")
                    .with_label(
                        Label::new(source, span, LabelType::Error)
                            .with_message(format!("found type {:?} ~ {:?}", var, ty)),
                    ),
            );
        }
        self.canonicalise(&mut ty);
        self.var_types.insert(var, ty);
        Dr::ok(self)
    }

    /// Returns true if the variable occurs in the given value.
    fn occurs_in(&self, var: &Var, val: &PartialValue) -> bool {
        match val {
            PartialValue::Let(_) => todo!(),
            PartialValue::Lambda(_) => todo!(),
            PartialValue::Apply(_) => todo!(),
            PartialValue::Var(var2) => var == var2,
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                self.occurs_in(var, parameter) || self.occurs_in(var, result)
            }
            _ => false,
        }
    }

    /// Assuming that there are no duplicates, return the union of the two unifications.
    // TODO: This assumption isn't actually necessarily true...?
    fn with(self, other: Self, source: Source, span: Span) -> Dr<Self> {
        other
            .var_types
            .into_iter()
            .fold(Dr::ok(self), |this, (var, val)| {
                this.bind(|this| this.with_var_type(source, span.clone(), var, val))
            })
            .map(|this| {
                other
                    .expr_types
                    .into_iter()
                    .fold(this, |this, (node_id, mut val)| {
                        this.canonicalise(&mut val);
                        this.with_expr_type(node_id, val)
                    })
            })
    }

    /// An idempotent operation reducing an value to a standard form.
    fn canonicalise(&self, val: &mut PartialValue) {
        match val {
            PartialValue::Let(_) => todo!(),
            PartialValue::Lambda(_) => todo!(),
            PartialValue::Apply(_) => todo!(),
            PartialValue::Var(var) => match self.var_types.get(var) {
                Some(PartialValue::Var(var2)) => *var = *var2,
                Some(value) => {
                    *val = value.clone();
                    self.canonicalise(val);
                }
                None => {}
            },
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                self.canonicalise(&mut *parameter);
                self.canonicalise(&mut *result);
            }
            _ => {}
        }
    }

    /// Unify the two partial values.
    /// If an error was found, the `report` function is called, which should generate a suitable report.
    /// The arguments are the canonicalised versions of `expected` and `found`.
    fn unify<R>(
        self,
        mut expected: PartialValue,
        mut found: PartialValue,
        source: Source,
        span: Span,
        report: R,
    ) -> Dr<Self>
    where
        R: FnOnce(&PartialValue, &PartialValue) -> Report,
    {
        // Recall everything we currently know about the two values we're dealing with.
        self.canonicalise(&mut expected);
        self.canonicalise(&mut found);

        // The report should only be called once, but it's easier to implement without this compile time restriction.
        // So we put it in an Option, and take it out when we need it.
        self.unify_recursive(
            source,
            span,
            &expected,
            &found,
            &expected,
            &found,
            &mut Some(report),
        )
    }

    /// Do not call this manually.
    /// Given canonicalised types, unify them.
    /// If the unification could not occur, the report is emitted using `base_expected` and `base_found`.
    #[allow(clippy::too_many_arguments)]
    fn unify_recursive<R>(
        self,
        source: Source,
        span: Span,
        base_expected: &PartialValue,
        base_found: &PartialValue,
        expected: &PartialValue,
        found: &PartialValue,
        report_box: &mut Option<R>,
    ) -> Dr<Self>
    where
        R: FnOnce(&PartialValue, &PartialValue) -> Report,
    {
        if let (
            PartialValue::FormFunc(FormFunc {
                parameter: expected_parameter,
                result: expected_result,
            }),
            PartialValue::FormFunc(FormFunc {
                parameter: found_parameter,
                result: found_result,
            }),
        ) = (expected, found)
        {
            // Unify the parameters and then the results.
            self.unify_recursive(
                source,
                span.clone(),
                base_expected,
                base_found,
                expected_parameter,
                found_parameter,
                report_box,
            )
            .bind(|this| {
                this.unify_recursive(
                    source,
                    span,
                    base_expected,
                    base_found,
                    expected_result,
                    found_result,
                    report_box,
                )
            })
        } else if let PartialValue::Var(found_var) = found {
            // Since we've canonicalised `found`, self.var_types.get(&found_var) is either None or Some(found_var).
            // We will replace this entry with `expected`.
            self.with_var_type(source, span, *found_var, expected.clone())
        } else if let PartialValue::Var(expected_var) = expected {
            // This is analogous to above.
            self.with_var_type(source, span, *expected_var, found.clone())
        } else {
            // We couldn't unify the two types.
            // We can still try to continue type inference, so we'll just return an error and choose not to unify anything.
            Dr::ok_with(
                self,
                report_box.take().expect("tried to create two reports")(base_expected, base_found),
            )
        }
    }

    fn expr_type(&self, expr: &Expr) -> PartialValue {
        self.expr_types[&expr.id()].clone()
    }
}

/// `locals` is the list of the types associated with each local.
/// The de Bruijn index `n` refers to the `n`th entry in this slice.
fn traverse(expr: &Expr, ctx: &mut TyCtx, locals: &[PartialValue]) -> Dr<Unification> {
    match &expr.contents {
        ExprContents::IntroLocal(IntroLocal(n)) => Dr::ok(Unification::new_with_expr_type(
            expr.id(),
            locals[n.0 as usize].clone(),
        )),
        ExprContents::IntroU64(_) => Dr::ok(Unification::new_with_expr_type(
            expr.id(),
            PartialValue::FormU64,
        )),
        ExprContents::IntroFalse(_) => todo!(),
        ExprContents::IntroTrue(_) => todo!(),
        ExprContents::IntroUnit(_) => Dr::ok(Unification::new_with_expr_type(
            expr.id(),
            PartialValue::FormUnit,
        )),
        ExprContents::FormU64(_) => todo!(),
        ExprContents::FormBool(_) => todo!(),
        ExprContents::FormUnit(_) => todo!(),
        ExprContents::Inst(_) => todo!(),
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
                        .with(to_assign_unif, ctx.source, expr.span())
                        .map(|unif| unif.with_expr_type(expr.id(), result_ty))
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
                body_unif.with_expr_type(expr.id(), func_ty)
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
                    ctx.source,
                    expr.span(),
                    |expected, found| {
                        Report::new(ReportKind::Error, ctx.source, expr.span().start)
                            .with_message("type mismatch when calling function")
                            .with_label(
                                Label::new(ctx.source, function.span(), LabelType::Error)
                                    .with_message(format!("the function had type {:?}", expected))
                                    .with_order(0),
                            )
                            .with_label(
                                if let PartialValue::FormFunc(FormFunc { parameter, .. }) = found {
                                    Label::new(ctx.source, function.span(), LabelType::Error)
                                        .with_message(format!(
                                            "the argument had type {:?}",
                                            parameter
                                        ))
                                        .with_order(10)
                                } else {
                                    panic!()
                                },
                            )
                    },
                )
                .map(|unif| unif.with_expr_type(expr.id(), PartialValue::Var(result_ty)))
            })
        }
        ExprContents::Var(_) => todo!(),
        ExprContents::FormFunc(_) => todo!(),
    }
}
