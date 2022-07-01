//! The kernel type checker.

use fcommon::{Dr, Label, LabelType, Report, ReportKind};
use fnodes::{
    definition::Definition,
    expr::{Expr, ExprContents, MetavariableGenerator},
};

mod defeq;
mod env;
mod infer;
mod unfold;
mod whnf;

pub use defeq::*;
pub use env::*;
pub use infer::*;
pub use unfold::*;
pub use whnf::*;

use crate::expr::first_local_or_metavariable;

/// Type checks a definition.
/// This function returns a [`CertifiedDefinition`], a definition that has been verified by the type checker.
pub fn check(env: &Environment, def: &Definition) -> Dr<CertifiedDefinition> {
    check_no_local_or_metavariable(env, &def.contents.ty).bind(|()| {
        // Since we have no metavariables in the given expression,
        // we can initialise the metavariable generator with any value.
        let mut meta_gen = MetavariableGenerator::new(None);
        // Check that the type of a definition is indeed a type.
        infer_type(env, &mut meta_gen, &def.contents.ty, true).bind(|sort| {
            as_sort(env, sort).bind(|sort| {
                if let Some(expr) = &def.contents.expr {
                    let expr = expr.clone();
                    check_no_local_or_metavariable(env, &expr).bind(|()| {
                        // Check that the type of the contents of the definition
                        // match the type declared in the definition.
                        infer_type(env, &mut meta_gen, &expr, true).bind(|ty| {
                            definitionally_equal(env, &mut meta_gen, &ty, &def.contents.ty).bind(
                                |types_equal| {
                                    if types_equal {
                                        Dr::ok(CertifiedDefinition::new(
                                            def.clone(),
                                            sort,
                                            ReducibilityHints::Opaque,
                                        ))
                                    } else {
                                        Dr::fail(Report::new(
                                            ReportKind::Error,
                                            env.source,
                                            expr.provenance.span().start,
                                        ).with_label(Label::new(env.source, expr.provenance.span(), LabelType::Error).with_message("this expression's type did not match the type declared in the definition")))
                                    }
                                },
                            )
                        })
                    })
                } else {
                    Dr::ok(CertifiedDefinition::new(
                        def.clone(),
                        sort,
                        ReducibilityHints::Opaque,
                    ))
                }
            })
        })
    })
}

fn check_no_local_or_metavariable(env: &Environment, e: &Expr) -> Dr<()> {
    if let Some(inner) = first_local_or_metavariable(&e) {
        return Dr::fail(
            Report::new(
                ReportKind::Error,
                env.source,
                e.provenance.span().start,
            )
            .with_label(
                Label::new(
                    env.source,
                    e.provenance.span(),
                    LabelType::Error,
                )
                .with_message("could not add definition to the environment as it contained an invalid expression"),
            ).with_label(Label::new(
                env.source,
                inner.provenance.span(),
                LabelType::Note,
            )
            .with_message(match &inner.contents {
                ExprContents::Metavariable(_) => "metavariable found here",
                ExprContents::LocalConstant(_) => "local constant found here",
                _ => unreachable!()
            }),),
        );
    } else {
        Dr::ok(())
    }
}
