use std::sync::Arc;

use fcommon::{Dr, Label, LabelType, Report, ReportKind, Source, Span};
use fkernel::{CertifiedModule, TypeChecker};
use fnodes::{
    basic_nodes::{DeBruijnIndex, Name, Provenance},
    definition::{Definition, DefinitionContents},
    expr::{Apply, Bound, Expr, ExprContents, Lambda, Pi, Sort},
    module::{Item, Module, ModuleContents},
    universe::{Universe, UniverseContents, UniverseSucc},
};
use qparse::{PDefinition, PExpr, PExprContents, PItem, PUniverse, PUniverseContents, QuillParser};

#[salsa::query_group(ElaboratorStorage)]
pub trait Elaborator: QuillParser + TypeChecker {
    fn elaborate(&self, source: Source) -> Dr<Arc<Module>>;
    fn elaborate_and_certify(&self, source: Source) -> Dr<Arc<CertifiedModule>>;
}

#[tracing::instrument(level = "trace")]
pub fn elaborate(db: &dyn Elaborator, source: Source) -> Dr<Arc<Module>> {
    db.parse_quill(source).bind(|items| {
        let mut module = Module {
            provenance: Provenance::Quill { source, span: 0..1 },
            contents: ModuleContents { items: Vec::new() },
        };
        let mut reports = Vec::new();
        for (item, span) in items.as_ref() {
            match item {
                PItem::Definition { def } => {
                    let (result, more_reports) =
                        elaborate_definition(db, source, def, span.clone()).destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        module.contents.items.push(Item::Definition(result))
                    }
                }
            }
        }
        Dr::ok_with_many(Arc::new(module), reports)
    })
}

#[tracing::instrument(level = "trace")]
pub fn elaborate_and_certify(db: &dyn Elaborator, source: Source) -> Dr<Arc<CertifiedModule>> {
    db.elaborate(source)
        .bind(|module| db.certify_module(source, module))
}

/// Attempt to convert a definition written in Quill code to Feather.
/// This process is known as *elaboration*; essentially, filling in the blanks of what the
/// programmer intended but did not explicitly write.
///
/// Once this elaboration is complete, the definition can be passed to Feather's kernel for
/// things like type checking.
#[tracing::instrument(level = "trace")]
fn elaborate_definition(
    db: &dyn Elaborator,
    source: Source,
    def: &PDefinition,
    span: Span,
) -> Dr<Definition> {
    elaborate_expr(db, source, &[], &def.ty).bind(|ty| {
        elaborate_expr(db, source, &[], &def.value).map(|expr| Definition {
            provenance: Provenance::Quill { source, span },
            contents: DefinitionContents {
                name: def.name.clone(),
                universe_params: Vec::new(),
                ty,
                expr: Some(expr),
            },
        })
    })
}

/// The list of `locals` is the list of bound variables.
/// Their index in the list is the associated [`DeBruijnIndex`].
fn elaborate_expr(db: &dyn Elaborator, source: Source, locals: &[Name], e: &PExpr) -> Dr<Expr> {
    match &e.contents {
        PExprContents::Lexical { text } => {
            let name = db.intern_string_data(text.clone());
            match locals
                .iter()
                .enumerate()
                .find(|(_, local)| local.contents == name)
            {
                Some((i, _)) => Dr::ok(Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Bound(Bound {
                        index: DeBruijnIndex::new(i as u32),
                    }),
                )),
                None => Dr::fail(
                    locals.iter().fold(
                        Report::new(ReportKind::Error, source, e.provenance.span().start)
                            .with_message(format!("could not find variable `{}`", text))
                            .with_label(
                                Label::new(source, e.provenance.span(), LabelType::Error)
                                    .with_message("error was found here, local variables visible from this expression are underlined"),
                            ),
                        |report, local| {
                            report.with_label(Label::new(
                                source,
                                local.provenance.span(),
                                LabelType::Note,
                            ).with_message(db.lookup_intern_string_data(local.contents)))
                        },
                    ),
                ),
            }
        }
        PExprContents::Apply { left, right } => {
            elaborate_expr(db, source, locals, left).bind(|left| {
                elaborate_expr(db, source, locals, right).map(|right| {
                    Expr::new_with_provenance(
                        &e.provenance,
                        ExprContents::Apply(Apply {
                            function: Box::new(left),
                            argument: Box::new(right),
                        }),
                    )
                })
            })
        }
        PExprContents::UnaryOp {
            operator,
            operator_span,
            param,
        } => todo!(),
        PExprContents::BinaryOp {
            operator,
            operator_span,
            left,
            right,
        } => todo!(),
        PExprContents::Forall { binder, inner_expr } => {
            elaborate_expr(db, source, locals, &binder.ty).bind(|ty| {
                let new_locals = std::iter::once(&binder.name)
                    .chain(locals)
                    .cloned()
                    .collect::<Vec<_>>();
                elaborate_expr(db, source, &new_locals, inner_expr).map(|inner_expr| {
                    Expr::new_with_provenance(
                        &e.provenance,
                        ExprContents::Pi(Pi {
                            parameter_name: binder.name.clone(),
                            binder_annotation: binder.binder_annotation,
                            parameter_ty: Box::new(ty),
                            result: Box::new(inner_expr),
                        }),
                    )
                })
            })
        }
        PExprContents::Function { binder, inner_expr } => {
            elaborate_expr(db, source, locals, &binder.ty).bind(|ty| {
                let new_locals = std::iter::once(&binder.name)
                    .chain(locals)
                    .cloned()
                    .collect::<Vec<_>>();
                elaborate_expr(db, source, &new_locals, inner_expr).map(|inner_expr| {
                    Expr::new_with_provenance(
                        &e.provenance,
                        ExprContents::Lambda(Lambda {
                            parameter_name: binder.name.clone(),
                            binder_annotation: binder.binder_annotation,
                            parameter_ty: Box::new(ty),
                            result: Box::new(inner_expr),
                        }),
                    )
                })
            })
        }
        PExprContents::Let {
            name_to_assign,
            to_assign,
            to_assign_ty,
            body,
        } => todo!(),
        PExprContents::Sort { universe } => elaborate_universe(db, source, universe)
            .map(|u| Expr::new_with_provenance(&e.provenance, ExprContents::Sort(Sort(u)))),
    }
}

fn elaborate_universe(db: &dyn Elaborator, source: Source, u: &PUniverse) -> Dr<Universe> {
    let provenance = u.provenance.clone();
    match &u.contents {
        PUniverseContents::Lexical { text } => match text.parse() {
            Ok(value) => Dr::ok((0..value).fold(
                Universe::new_with_provenance(&provenance, UniverseContents::UniverseZero),
                |u, _| {
                    Universe::new_with_provenance(
                        &provenance,
                        UniverseContents::UniverseSucc(UniverseSucc(Box::new(u))),
                    )
                },
            )),
            Err(_) => todo!(),
        },
    }
}
