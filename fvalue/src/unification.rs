use fnodes::basic_nodes::ShadowGenerator;

use crate::*;

/// Do not mutate any values in `TyCtx` except for `print`, which may be used mutably.
pub struct TyCtx<'a> {
    pub db: &'a dyn ValueInferenceEngine,
    pub source: Source,
    pub var_gen: VarGenerator,
    pub shadow_gen: ShadowGenerator,
    pub known_local_types: &'a NodeInfoContainer<ExprContents, PartialExprTy>,
    pub print: PartialValuePrinter<'a>,
    pub infos: &'a DefaultInfos,
}

/// Represents the types of known expressions and type variables at some stage in type inference.
/// Any methods that return a [`Vec<Label>`] are diagnostic methods; if they return a non-empty list,
/// the labels should be attached to a [`Report`] and encased in a [`Dr`].
#[derive(Debug, Default)]
pub struct Unification {
    /// The known types of each expression, at this point in inference.
    expr_types: HashMap<NodeId, PartialValue>,
    /// A map converting a variable into a canonical representation.
    var_values: HashMap<Var, PartialValue>,

    pending_coercions: Vec<PendingCoercion>,
}

/// A coercion that we were asked to do, but could not perform right away.
/// This occurs when either the expression or the target is an inference variable.
#[derive(Debug)]
pub struct PendingCoercion {
    /// The cause is used to format the report that we will create if the coercion fails.
    pub cause: Span,
    pub value: PartialValue,
    pub var: Var,
    /// If this is true, we are coercing the variable into the value.
    /// If this is false, we are coercing the value into the variable.
    pub coerce_var_to_value: bool,
}

impl PendingCoercion {
    pub fn source(&self) -> PartialValue {
        if self.coerce_var_to_value {
            PartialValue::Var(self.var)
        } else {
            self.value.clone()
        }
    }

    pub fn target(&self) -> PartialValue {
        if self.coerce_var_to_value {
            self.value.clone()
        } else {
            PartialValue::Var(self.var)
        }
    }
}

impl Unification {
    /// Construct a blank unification that contains only the information for a single expression.
    pub fn new_with_expr_type(expr: &Expr, ty: PartialValue) -> Self {
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
    pub fn with_expr_type(mut self, expr: &Expr, ty: PartialValue) -> Self {
        self.insert_expr_type(expr, ty);
        self
    }

    /// Record the type of a single inference variable.
    /// If this causes an occurs check to fail, which can happen with circularly defined types,
    /// an error will be emitted.
    pub fn insert_var_type(
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
        if let Some(previous_inference) = self.var_values.insert(var, ty) {
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
    pub fn variables_occuring_in(&self, val: &PartialValue) -> HashSet<Var> {
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
    pub fn with(mut self, other: Self, ctx: &mut TyCtx, span: Span) -> Dr<Self> {
        let mut labels = Vec::new();
        for (var, ty) in other.var_values {
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
    pub fn canonicalise(&self, val: &mut PartialValue) {
        match val {
            PartialValue::Var(var) => match self.var_values.get(var) {
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
    pub fn unify<R>(
        mut self,
        mut expected: PartialValue,
        mut found: PartialValue,
        ctx: &mut TyCtx,
        span: Span,
        report: R,
    ) -> Dr<Self>
    where
        R: FnOnce(&mut TyCtx, &Self, &PartialValue, &PartialValue) -> Report,
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
            let labels = labels
                .into_iter()
                .fold(report(ctx, &self, &expected, &found), |report, label| {
                    report.with_label(label)
                });
            Dr::ok_with(self, labels)
        }
        .bind(|unif| unif.process_pending_coercions(ctx))
    }

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
                    parameter_name: expected_parameter_name,
                    parameter_ty: expected_parameter,
                    result: expected_result,
                }),
                PartialValue::FormFunc(FormFunc {
                    parameter_name: found_parameter_name,
                    parameter_ty: found_parameter,
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
                // Make sure that the function parameter names match.
                found_result.alpha_convert(*found_parameter_name, *expected_parameter_name);
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
            (
                PartialValue::FormCoproduct(FormCoproduct {
                    variants: expected_variants,
                }),
                PartialValue::FormCoproduct(FormCoproduct {
                    variants: found_variants,
                }),
            ) => {
                // TODO: Enhance this check to work out if there were missing or mistyped variants.
                if expected_variants.len() != found_variants.len() {
                    vec![Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(
                            format!(
                                "coproduct types {} and {} had differing amounts of variants, so could not be compared",
                                ctx.print.print(expected),
                                ctx.print.print(found)
                            )
                        )]
                } else {
                    let mut labels = Vec::new();
                    for (expected, found) in expected_variants.iter().zip(found_variants) {
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
            (
                PartialValue::FormCoproduct(FormCoproduct { variants }),
                PartialValue::FormAnyCoproduct(FormAnyCoproduct { known_variant }),
            ) => {
                if let Some(variant) = variants
                    .iter()
                    .find(|variant| variant.name == known_variant.name)
                {
                    self.unify_recursive(ctx, span, &variant.ty, &known_variant.ty)
                } else {
                    vec![Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(format!(
                            "coproduct type {} did not contain a field named {}",
                            ctx.print.print(expected),
                            ctx.db.lookup_intern_string_data(known_variant.name)
                        ))]
                }
            }
            (
                PartialValue::FormAnyCoproduct(FormAnyCoproduct { known_variant }),
                PartialValue::FormCoproduct(FormCoproduct { variants }),
            ) => {
                if let Some(variant) = variants
                    .iter()
                    .find(|variant| variant.name == known_variant.name)
                {
                    self.unify_recursive(ctx, span, &known_variant.ty, &variant.ty)
                } else {
                    vec![Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(format!(
                            "coproduct type {} did not contain a field named {}",
                            ctx.print.print(found),
                            ctx.db.lookup_intern_string_data(known_variant.name)
                        ))]
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

    /// Try to execute any pending coercions, if we know an updated value of an inference variable.
    fn process_pending_coercions(mut self, ctx: &mut TyCtx) -> Dr<Unification> {
        // TODO: We should optimise this if necessary.
        // We're probably performing too many coercion checks.
        trace!("processing pending coercions");
        let coercions = std::mem::take(&mut self.pending_coercions);
        coercions.into_iter().fold(Dr::ok(self), |unif, coercion| {
            unif.bind(|unif| {
                unif.coerce_into(
                    coercion.source(),
                    coercion.target(),
                    ctx,
                    coercion.cause.clone(),
                    |ctx, expected, found| {
                        Report::new(ReportKind::Error, ctx.source, coercion.cause.clone().start)
                            .with_message("type mismatch during type coercion")
                            .with_label(
                                Label::new(ctx.source, coercion.cause.clone(), LabelType::Error)
                                    .with_message(format!(
                                        "tried to coerce {} into {}",
                                        ctx.print.print(if coercion.coerce_var_to_value {
                                            expected
                                        } else {
                                            found
                                        }),
                                        ctx.print.print(if coercion.coerce_var_to_value {
                                            found
                                        } else {
                                            expected
                                        })
                                    )),
                            )
                    },
                )
            })
        })
    }

    /// In order to remove all pending coercions, just set the two values to equal each other.
    /// After this function call, we will have no pending coercions.
    pub fn finish_performing_coercions(mut self, ctx: &mut TyCtx) -> Dr<Unification> {
        let coercions = std::mem::take(&mut self.pending_coercions);
        tracing::debug!("pending: {:#?}", coercions);
        coercions.into_iter().fold(Dr::ok(self), |unif, coercion| {
            unif.bind(|unif| {
                unif.unify(
                    PartialValue::Var(coercion.var),
                    coercion.value,
                    ctx,
                    coercion.cause.clone(),
                    |ctx, _, expected, found| {
                        Report::new(ReportKind::Error, ctx.source, coercion.cause.clone().start)
                            .with_message("type mismatch during type coercion")
                            .with_label(
                                Label::new(ctx.source, coercion.cause.clone(), LabelType::Error)
                                    .with_message(format!(
                                        "tried to unify {} with {}",
                                        ctx.print.print(if coercion.coerce_var_to_value {
                                            expected
                                        } else {
                                            found
                                        }),
                                        ctx.print.print(if coercion.coerce_var_to_value {
                                            found
                                        } else {
                                            expected
                                        })
                                    )),
                            )
                            .with_note("the rest of the expression has already been type checked, so this coercion was weakened to a unification")
                    },
                )
            })
        })
    }

    pub fn expr_type(&self, expr: &Expr) -> PartialValue {
        let mut result = self.expr_types[&expr.id()].clone();
        self.canonicalise(&mut result);
        result
    }

    /// Convert this expression into a partial value.
    /// This essentially discards the provenance of the expression and keeps just its value.
    pub fn expr_to_value(&self, expr: &Expr, ctx: &mut TyCtx) -> PartialValue {
        match &expr.contents {
            ExprContents::IntroLocal(local) => PartialValue::IntroLocal(*local),
            ExprContents::IntroU64(_) => todo!(),
            ExprContents::IntroFalse => todo!(),
            ExprContents::IntroTrue => todo!(),
            ExprContents::IntroUnit => todo!(),
            ExprContents::FormU64 => PartialValue::FormU64,
            ExprContents::FormBool => todo!(),
            ExprContents::FormUnit => PartialValue::FormUnit,
            ExprContents::IntroProduct(_) => todo!(),
            ExprContents::FormProduct(FormProduct { fields }) => {
                PartialValue::FormProduct(FormProduct {
                    fields: fields
                        .iter()
                        .map(|field| ComponentContents {
                            name: field.contents.name.contents,
                            ty: self.expr_to_value(&field.contents.ty, ctx),
                        })
                        .collect(),
                })
            }
            ExprContents::MatchProduct(_) => todo!(),
            ExprContents::IntroCoproduct(_) => todo!(),
            ExprContents::FormCoproduct(FormCoproduct { variants }) => {
                PartialValue::FormCoproduct(FormCoproduct {
                    variants: variants
                        .iter()
                        .map(|field| ComponentContents {
                            name: field.contents.name.contents,
                            ty: self.expr_to_value(&field.contents.ty, ctx),
                        })
                        .collect(),
                })
            }
            ExprContents::FormAnyCoproduct(_) => todo!(),
            ExprContents::MatchCoproduct(_) => todo!(),
            ExprContents::ReduceTy(_) => todo!(),
            ExprContents::ExpandTy(_) => todo!(),
            ExprContents::Inst(Inst(qn)) => {
                PartialValue::Inst(Inst(ctx.db.qualified_name_to_path(qn)))
            }
            ExprContents::Let(_) => todo!(),
            ExprContents::Lambda(_) => todo!(),
            ExprContents::Apply(_) => todo!(),
            ExprContents::Var(var) => PartialValue::Var(*var),
            ExprContents::FormFunc(FormFunc {
                parameter_name,
                parameter_ty,
                result,
            }) => PartialValue::FormFunc(FormFunc {
                parameter_name: Shadow::<Str>::from(parameter_name),
                parameter_ty: Box::new(self.expr_to_value(parameter_ty, ctx)),
                result: Box::new(self.expr_to_value(result, ctx)),
            }),
            ExprContents::FormUniverse => todo!(),
        }
    }

    /// Try to evaluate this expression and check that it equals the given expression, given all relevant types.
    /// If an error was found, the `report` function is called, which should generate a suitable report.
    /// The arguments are the canonicalised versions of `expected` and `found`.
    pub fn coerce_into<R>(
        mut self,
        mut expr: PartialValue,
        mut target: PartialValue,
        ctx: &mut TyCtx,
        span: Span,
        report: R,
    ) -> Dr<Self>
    where
        R: FnOnce(&mut TyCtx, &PartialValue, &PartialValue) -> Report,
    {
        // Recall everything we currently know about the two values we're dealing with.
        self.canonicalise(&mut expr);
        self.canonicalise(&mut target);

        trace!("coercing {:?} into {:?}", expr, target);

        // The report should only be called once, but it's easier to implement without this compile time restriction.
        // So we put it in an Option, and take it out when we need it.
        let labels = self.coerce_into_inner(&expr, &target, ctx, span);
        if labels.is_empty() {
            Dr::ok(self)
        } else {
            Dr::ok_with(
                self,
                labels
                    .into_iter()
                    .fold(report(ctx, &expr, &target), |report, label| {
                        report.with_label(label)
                    }),
            )
        }
    }

    // TODO: Have a maximum calculation depth, after which computation should stop.
    pub fn coerce_into_inner(
        &mut self,
        expr: &PartialValue,
        target: &PartialValue,
        ctx: &mut TyCtx,
        span: Span,
    ) -> Vec<Label> {
        if expr == target {
            return Vec::new();
        }

        if let PartialValue::Var(var) = expr {
            // We can't perform the coercion right away.
            self.pending_coercions.push(PendingCoercion {
                cause: span,
                value: target.clone(),
                var: *var,
                coerce_var_to_value: true,
            });
            return Vec::new();
        }
        if let PartialValue::Var(var) = target {
            self.pending_coercions.push(PendingCoercion {
                cause: span,
                value: expr.clone(),
                var: *var,
                coerce_var_to_value: false,
            });
            return Vec::new();
        }

        if let (
            PartialValue::FormProduct(FormProduct {
                fields: expr_fields,
            }),
            PartialValue::FormProduct(FormProduct {
                fields: target_fields,
            }),
        ) = (expr, target)
        {
            if expr_fields.len() != target_fields.len() {
                return vec![
                    Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(
                            format!(
                                "product types {} and {} had differing amounts of fields, so could not be compared",
                                ctx.print.print(expr),
                                ctx.print.print(target)
                            )
                        )
                ];
            }
            return expr_fields
                .iter()
                .zip(target_fields)
                .flat_map(|(expr_field, target_field)| {
                    if expr_field.name != target_field.name {
                        vec![
                            Label::new(ctx.source, span.clone(), LabelType::Error).with_message(
                                format!(
                                    "field names {} and {} did not match",
                                    ctx.db.lookup_intern_string_data(expr_field.name),
                                    ctx.db.lookup_intern_string_data(target_field.name),
                                ),
                            ),
                        ]
                    } else {
                        self.coerce_into_inner(&expr_field.ty, &target_field.ty, ctx, span.clone())
                    }
                })
                .collect();
        }

        if let (
            PartialValue::FormCoproduct(FormCoproduct {
                variants: expr_variants,
            }),
            PartialValue::FormCoproduct(FormCoproduct {
                variants: target_variants,
            }),
        ) = (expr, target)
        {
            if expr_variants.len() != target_variants.len() {
                return vec![
                    Label::new(ctx.source, span, LabelType::Note)
                        .with_order(1000)
                        .with_message(
                            format!(
                                "coproduct types {} and {} had differing amounts of variants, so could not be compared",
                                ctx.print.print(expr),
                                ctx.print.print(target)
                            )
                        )
                ];
            }
            return expr_variants
                .iter()
                .zip(target_variants)
                .flat_map(|(expr_variant, target_variant)| {
                    if expr_variant.name != target_variant.name {
                        vec![
                            Label::new(ctx.source, span.clone(), LabelType::Error).with_message(
                                format!(
                                    "variant names {} and {} did not match",
                                    ctx.db.lookup_intern_string_data(expr_variant.name),
                                    ctx.db.lookup_intern_string_data(target_variant.name),
                                ),
                            ),
                        ]
                    } else {
                        self.coerce_into_inner(
                            &expr_variant.ty,
                            &target_variant.ty,
                            ctx,
                            span.clone(),
                        )
                    }
                })
                .collect();
        }

        if let (
            PartialValue::FormCoproduct(FormCoproduct {
                variants: expr_variants,
            }),
            PartialValue::FormAnyCoproduct(FormAnyCoproduct { known_variant }),
        ) = (expr, target)
        {
            if let Some(expr_variant) = expr_variants
                .iter()
                .find(|variant| variant.name == known_variant.name)
            {
                return self.coerce_into_inner(&expr_variant.ty, &known_variant.ty, ctx, span);
            } else {
                return vec![
                    Label::new(ctx.source, span, LabelType::Error).with_message(format!(
                        "coproduct type {} did not contain a variant with name {}",
                        ctx.print.print(target),
                        ctx.db.lookup_intern_string_data(known_variant.name),
                    )),
                ];
            }
        }

        if let PartialValue::Inst(Inst(path)) = expr {
            // Instance the variable from this path.
            // TODO: We probably need to know types, but a priori we don't actually know them at this point.
            let (source, def_name) = ctx.db.split_path_last(*path);
            if let Some(module) = ctx
                .db
                .module_from_feather_source(Source {
                    path: source,
                    ty: SourceType::Feather,
                })
                .value()
            {
                if let Some(def) = module
                    .module
                    .contents
                    .defs
                    .iter()
                    .find(|def| def.contents.name.contents == def_name)
                {
                    let def_value = self.expr_to_value(&def.contents.expr, ctx);
                    return self.coerce_into_inner(&def_value, target, ctx, span);
                }
            }
        }

        vec![
            Label::new(ctx.source, span, LabelType::Note).with_message(format!(
                "could not coerce type {} into type {}",
                ctx.print.print(expr),
                ctx.print.print(target),
            )),
        ]
    }
}
