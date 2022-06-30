//! Infers types of expressions.

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Span};
use fnodes::{expr::*, universe::*};

use crate::expr::{closed, has_free_variables, instantiate_universe_parameters};

use super::env::Environment;

/// Infers the type of an expression. Invoke with a closed expression.
/// If `check` is true, we also perform some type checking, but the return value is not changed.
/// If the expression is type-correct, the return value is the expression's type, and further,
/// if `check` is true and the return value is not an error, the expression is type-correct.
pub fn infer_type(env: &Environment, e: &Expr, check: bool) -> Dr<Expr> {
    if has_free_variables(e) {
        return Dr::fail(
            Report::new(ReportKind::Error, env.source, e.provenance.span().start).with_label(
                Label::new(env.source, e.provenance.span(), LabelType::Error).with_message(
                    "could not infer type of expression because it had free variables",
                ),
            ),
        );
    }

    let result = match &e.contents {
        ExprContents::Bound(bound) => return Dr::ok(*bound.ty.clone()),
        ExprContents::Inst(inst) => infer_type_inst(env, e.provenance.span(), check, inst),
        ExprContents::Let(_) => todo!(),
        ExprContents::Lambda(_) => todo!(),
        ExprContents::Pi(_) => todo!(),
        ExprContents::Apply(_) => todo!(),
        ExprContents::Sort(_) => todo!(),
        ExprContents::Metavariable(var) => return Dr::ok(*var.ty.clone()),
        ExprContents::LocalConstant(_) => todo!(),
    };

    match result {
        Ok(val) => Dr::ok(val),
        Err(err) => Dr::fail(err(Report::new(
            ReportKind::Error,
            env.source,
            e.provenance.span().start,
        ))),
    }
}

fn infer_type_inst<'a>(
    env: &'a Environment,
    span: Span,
    check: bool,
    inst: &'a Inst,
) -> Result<Expr, Box<dyn FnOnce(Report) -> Report + 'a>> {
    let path = inst.name.to_path(env.intern);
    match env.definitions.get(&path) {
        Some(def) => {
            if def.contents.universe_params.len() == inst.universes.len() {
                let mut e = def.contents.ty.clone();
                instantiate_universe_parameters(
                    &mut e,
                    &def.contents.universe_params,
                    &inst.universes,
                );
                Ok(e)
            } else {
                Err(Box::new(move |report| {
                    report
                        .with_label(Label::new(env.source, span, LabelType::Error).with_message(
                            format!(
                                "definition {} has {} universe parameters, but {} were supplied",
                                path.display(env.intern),
                                def.contents.universe_params.len(),
                                inst.universes.len()
                            ),
                        ))
                        .with_label(
                            Label::new(
                                def.provenance.source().unwrap_or(env.source),
                                def.provenance.span(),
                                LabelType::Note,
                            )
                            .with_message(format!("{} defined here", path.display(env.intern),)),
                        )
                }))
            }
        }
        None => Err(Box::new(move |report| {
            report
                .with_label(Label::new(env.source, span, LabelType::Error))
                .with_message(format!(
                    "definition {} could not be found in the environment",
                    path.display(env.intern)
                ))
        })),
    }
}
