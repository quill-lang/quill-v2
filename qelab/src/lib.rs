use std::{collections::HashMap, sync::Arc};

use fcommon::{Dr, Label, LabelType, Path, Report, ReportKind, Source, Span};
use fkernel::{
    inductive::CertifiedInductive,
    typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment},
    CertifiedModule, TypeChecker,
};
use fnodes::{
    basic_nodes::{DeBruijnIndex, Name, Provenance},
    definition::{Definition, DefinitionContents},
    expr::{Apply, Bound, Expr, ExprContents, Inst, Lambda, Pi, Sort},
    universe::{Universe, UniverseContents, UniverseSucc, UniverseVariable},
};
use qparse::{PDefinition, PExpr, PExprContents, PItem, PUniverse, PUniverseContents, QuillParser};

#[salsa::query_group(ElaboratorStorage)]
pub trait Elaborator: QuillParser + TypeChecker {
    fn elaborate_and_certify(&self, source: Source) -> Dr<Arc<CertifiedModule>>;
}

#[tracing::instrument(level = "trace")]
pub fn elaborate_and_certify(db: &dyn Elaborator, source: Source) -> Dr<Arc<CertifiedModule>> {
    db.parse_quill(source).bind(|items| {
        let source_path = db.lookup_intern_path_data(source.path);
        let mut definitions = Vec::<CertifiedDefinition>::new();
        let mut inductives = Vec::<CertifiedInductive>::new();
        let mut reports = Vec::new();
        for (item, span) in items.as_ref() {
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
                PItem::Definition { def } => {
                    let env = Environment {
                        source,
                        db: db.up(),
                        definitions: local_definitions,
                        inductives: local_inductives,
                        universe_variables: &def.universe_params,
                    };

                    let (result, more_reports) = elaborate_definition(&env, def, span.clone())
                        .bind(|def| typeck::check(&env, &def, DefinitionOrigin::Feather))
                        .destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        definitions.push(result);
                    }
                } /* Item::Inductive(ind) => {
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
                  } */
            }
        }
        Dr::ok_with_many(
            Arc::new(CertifiedModule {
                provenance: Provenance::Quill { source, span: 0..1 },
                definitions,
                inductives,
            }),
            reports,
        )
    })
}

/// Attempt to convert a definition written in Quill code to Feather.
/// This process is known as *elaboration*; essentially, filling in the blanks of what the
/// programmer intended but did not explicitly write.
///
/// Once this elaboration is complete, the definition can be passed to Feather's kernel for
/// things like type checking.
#[tracing::instrument(level = "trace")]
fn elaborate_definition(env: &Environment, def: &PDefinition, span: Span) -> Dr<Definition> {
    elaborate_expr(env, &[], &def.ty).bind(|ty| {
        elaborate_expr(env, &[], &def.value).map(|expr| Definition {
            provenance: Provenance::Quill {
                source: env.source,
                span,
            },
            contents: DefinitionContents {
                name: def.name.clone(),
                universe_params: def.universe_params.clone(),
                ty,
                expr: Some(expr),
            },
        })
    })
}

/// The list of `locals` is the list of bound variables.
/// Their index in the list is the associated [`DeBruijnIndex`].
fn elaborate_expr(env: &Environment, locals: &[Name], e: &PExpr) -> Dr<Expr> {
    match &e.contents {
        PExprContents::QualifiedName {
            qualified_name,
            universes,
        } => {
            if qualified_name.segments.len() == 1 {
                // This is a local variable.
                let name = &qualified_name.segments[0];
                match locals
                    .iter()
                    .enumerate()
                    .find(|(_, local)| local.contents == name.contents)
                {
                    Some((i, _)) => Dr::ok(Expr::new_with_provenance(
                        &e.provenance,
                        ExprContents::Bound(Bound {
                            index: DeBruijnIndex::new(i as u32),
                        }),
                    )),
                    None => Dr::fail(
                        locals.iter().fold(
                            Report::new(ReportKind::Error, env.source, e.provenance.span().start)
                                .with_message(format!("could not find variable `{}`", env.db.lookup_intern_string_data(name.contents)))
                                .with_label(
                                    Label::new(env.source, e.provenance.span(), LabelType::Error)
                                        .with_message("error was found here, local variables visible from this expression are underlined").with_priority(1000),
                                ),
                            |report, local| {
                                report.with_label(Label::new(
                                    env.source,
                                    local.provenance.span(),
                                    LabelType::Note,
                                ).with_message(env.db.lookup_intern_string_data(local.contents)))
                            },
                        ),
                    ),
                }
            } else {
                // This is the name of a definition.
                Dr::sequence(universes.iter().map(|u| elaborate_universe(env, u))).map(
                    |universes| {
                        Expr::new_with_provenance(
                            &e.provenance,
                            ExprContents::Inst(Inst {
                                name: qualified_name.clone(),
                                universes,
                            }),
                        )
                    },
                )
            }
        }
        PExprContents::Apply { left, right } => elaborate_expr(env, locals, left).bind(|left| {
            elaborate_expr(env, locals, right).map(|right| {
                Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Apply(Apply {
                        function: Box::new(left),
                        argument: Box::new(right),
                    }),
                )
            })
        }),
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
        PExprContents::Forall { binder, inner_expr } => elaborate_expr(env, locals, &binder.ty)
            .bind(|ty| {
                let new_locals = std::iter::once(&binder.name)
                    .chain(locals)
                    .cloned()
                    .collect::<Vec<_>>();
                elaborate_expr(env, &new_locals, inner_expr).map(|inner_expr| {
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
            }),
        PExprContents::Function { binder, inner_expr } => elaborate_expr(env, locals, &binder.ty)
            .bind(|ty| {
                let new_locals = std::iter::once(&binder.name)
                    .chain(locals)
                    .cloned()
                    .collect::<Vec<_>>();
                elaborate_expr(env, &new_locals, inner_expr).map(|inner_expr| {
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
            }),
        PExprContents::Let {
            name_to_assign,
            to_assign,
            to_assign_ty,
            body,
        } => todo!(),
        PExprContents::Sort { universe } => elaborate_universe(env, universe)
            .map(|u| Expr::new_with_provenance(&e.provenance, ExprContents::Sort(Sort(u)))),
    }
}

fn elaborate_universe(env: &Environment, u: &PUniverse) -> Dr<Universe> {
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
            Err(_) => Dr::ok(Universe::new_with_provenance(
                &provenance,
                UniverseContents::UniverseVariable(UniverseVariable(
                    env.db.intern_string_data(text.to_owned()),
                )),
            )),
        },
    }
}
