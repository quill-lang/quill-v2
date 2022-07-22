use std::{collections::HashMap, sync::Arc};

use fcommon::{Dr, Label, LabelType, Path, PathData, Report, ReportKind, Source, Span};
use fkernel::{
    inductive::{self, CertifiedInductive},
    typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment},
    CertifiedModule, TypeChecker,
};
use fnodes::{
    basic_nodes::{DeBruijnIndex, Name, Provenance, QualifiedName},
    definition::{Definition, DefinitionContents},
    expr::{Apply, Borrow, Bound, Delta, Expr, ExprContents, Inst, Lambda, Let, Pi, Region, Sort},
    inductive::{Inductive, InductiveContents, IntroRule},
    universe::{Universe, UniverseContents, UniverseSucc, UniverseVariable},
};
use qparse::{
    PDefinition, PExpr, PExprContents, PInductive, PItem, PUniverse, PUniverseContents, QuillParser,
};

#[salsa::query_group(ElaboratorStorage)]
pub trait Elaborator: QuillParser + TypeChecker {
    fn elaborate_and_certify(
        &self,
        source: Source,
        file_contents: Arc<String>,
    ) -> Dr<Arc<CertifiedModule>>;
}

#[tracing::instrument(level = "trace", skip(file_contents))]
pub fn elaborate_and_certify(
    db: &dyn Elaborator,
    source: Source,
    file_contents: Arc<String>,
) -> Dr<Arc<CertifiedModule>> {
    db.parse_quill(source, file_contents).bind(|items| {
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
                }
                PItem::Inductive { ind } => {
                    let env = Environment {
                        source,
                        db: db.up(),
                        definitions: local_definitions,
                        inductives: local_inductives,
                        universe_variables: &ind.universe_params,
                    };
                    let (result, more_reports) = elaborate_inductive(&env, ind, span.clone())
                        .bind(|ind| inductive::check_inductive_type(env, &ind))
                        .destructure();
                    reports.extend(more_reports);
                    if let Some(result) = result {
                        // tracing::info!("{:#?}", result);
                        definitions.push(result.type_declaration);
                        for intro_rule in result.intro_rules {
                            definitions.push(intro_rule);
                        }
                        definitions.push(result.recursor);
                        definitions.push(result.squash);
                        inductives.push(result.inductive);
                        if let Some(result) = result.squashed_type {
                            definitions.push(result.type_declaration);
                            for intro_rule in result.intro_rules {
                                definitions.push(intro_rule);
                            }
                            definitions.push(result.recursor);
                            definitions.push(result.squash);
                            inductives.push(result.inductive);
                        }
                    }
                }
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
    let env = ElabEnv {
        env,
        extra_defs: HashMap::new(),
    };
    elaborate_expr(&env, &[], &def.ty).bind(|ty| {
        elaborate_expr(&env, &[], &def.value).map(|expr| Definition {
            provenance: Provenance::Quill {
                source: env.env.source,
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

/// Attempt to convert an inductive data type written in Quill code to Feather.
///
/// Once this elaboration is complete, the inductive can be passed to Feather's kernel for
/// things like type checking and construction of the eliminator.
#[tracing::instrument(level = "trace")]
fn elaborate_inductive(env: &Environment, ind: &PInductive, span: Span) -> Dr<Inductive> {
    let mut env = ElabEnv {
        env,
        extra_defs: HashMap::new(),
    };
    elaborate_expr(&env, &[], &ind.ty).bind(|ty| {
        // The environment used here doesn't know about the inductive.
        // We therefore need to add it into the elaboration environment now.
        env.extra_defs.insert(
            env.env.db.intern_path_data(PathData(
                env.env
                    .db
                    .lookup_intern_path_data(env.env.source.path)
                    .0
                    .into_iter()
                    .chain(std::iter::once(ind.name.contents))
                    .collect(),
            )),
            ty.clone(),
        );
        Dr::sequence(ind.intro_rules.iter().map(|(name, intro_rule_ty)| {
            elaborate_expr(&env, &[], intro_rule_ty).map(|ty| IntroRule {
                name: name.clone(),
                ty,
            })
        }))
        .map(|intro_rules| Inductive {
            provenance: ind.name.provenance.clone(),
            contents: InductiveContents {
                name: ind.name.clone(),
                universe_params: ind.universe_params.clone(),
                ty,
                global_params: ind.global_params,
                intro_rules,
            },
        })
    })
}

struct ElabEnv<'a> {
    env: &'a Environment<'a>,
    /// Extra definitions that we know exist but that have not yet been certified.
    /// The value associated to each key is the type of the definition.
    extra_defs: HashMap<Path, Expr>,
}

/// The list of `locals` is the list of bound variables.
/// Their index in the list is the associated [`DeBruijnIndex`].
fn elaborate_expr(env: &ElabEnv, locals: &[Name], e: &PExpr) -> Dr<Expr> {
    match &e.contents {
        PExprContents::QualifiedName {
            qualified_name,
            universes,
        } => match resolve_name(env, locals, qualified_name) {
            Some(ResolvedName::Bound(index)) => Dr::ok(Expr::new_with_provenance(
                &qualified_name.provenance,
                ExprContents::Bound(Bound { index }),
            )),
            Some(ResolvedName::QualifiedName(qualified_name)) => Dr::sequence(
                universes.iter().map(|u| elaborate_universe(env, u)),
            )
            .map(|universes| {
                Expr::new_with_provenance(
                    &e.provenance,
                    ExprContents::Inst(Inst {
                        name: qualified_name,
                        universes,
                    }),
                )
            }),
            None => Dr::fail(
                locals.iter().fold(
                    Report::new(ReportKind::Error, env.env.source, qualified_name.provenance.span().start)
                        .with_message(format!("could not find variable `{}`", qualified_name.display(env.env.db.up())))
                        .with_label(
                            Label::new(env.env.source, qualified_name.provenance.span(), LabelType::Error)
                                .with_message("error was found here, local variables visible from this expression are underlined").with_priority(1000),
                        ),
                    |report, local| {
                        report.with_label(Label::new(
                            env.env.source,
                            local.provenance.span(),
                            LabelType::Note,
                        ).with_message(env.env.db.lookup_intern_string_data(local.contents)))
                    },
                ),
            )
        },
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
        } => elaborate_expr(env, locals, to_assign_ty).bind(|to_assign_ty| {
            elaborate_expr(env, locals, to_assign).bind(|to_assign| {
                let new_locals = std::iter::once(name_to_assign)
                    .chain(locals)
                    .cloned()
                    .collect::<Vec<_>>();
                elaborate_expr(env, &new_locals, body).map(|body| {
                    Expr::new_with_provenance(
                        &e.provenance,
                        ExprContents::Let(Let {
                            name_to_assign: name_to_assign.clone(),
                            to_assign: Box::new(to_assign),
                            to_assign_ty: Box::new(to_assign_ty),
                            body: Box::new(body),
                        }),
                    )
                })
            })
        }),
        PExprContents::Borrow { region, value } =>
        elaborate_expr(env, locals, region).bind(|region|
            elaborate_expr(env, locals, value).map(|value| Expr::new_with_provenance(&e.provenance, ExprContents::Borrow(Borrow {
                region: Box::new(region),
                value: Box::new(value),
            })))),
        PExprContents::Borrowed { region, ty } =>
        elaborate_expr(env, locals, region).bind(|region|
            elaborate_expr(env, locals, ty).map(|ty| Expr::new_with_provenance(&e.provenance, ExprContents::Delta(Delta {
                region: Box::new(region),
                ty: Box::new(ty),
            })))),
        PExprContents::Sort { universe } => elaborate_universe(env, universe)
            .map(|u| Expr::new_with_provenance(&e.provenance, ExprContents::Sort(Sort(u)))),
        PExprContents::Region => Dr::ok(Expr::new_with_provenance(&e.provenance, ExprContents::Region(Region))),
    }
}

enum ResolvedName {
    QualifiedName(QualifiedName),
    Bound(DeBruijnIndex),
}

fn resolve_name(
    env: &ElabEnv,
    locals: &[Name],
    qualified_name: &QualifiedName,
) -> Option<ResolvedName> {
    if qualified_name.segments.len() == 1 {
        // This may be a local variable.
        // Construct the relevant de Bruijn index for this local.
        let name = &qualified_name.segments[0];
        if let Some((i, _)) = locals
            .iter()
            .enumerate()
            .find(|(_, local)| local.contents == name.contents)
        {
            return Some(ResolvedName::Bound(DeBruijnIndex::new(i as u32)));
        }
    }

    let attempt = |qualified_name: QualifiedName| {
        let path = qualified_name.to_path(env.env.db.up());
        if env.env.definitions.contains_key(&path) || env.extra_defs.contains_key(&path) {
            Some(ResolvedName::QualifiedName(qualified_name))
        } else {
            None
        }
    };

    // This is the name of a definition.
    // Try to resolve it.
    if let Some(result) = attempt(qualified_name.clone()) {
        return Some(result);
    }

    // Try to prepend all imported namespaces.
    let mut new_name = qualified_name.clone();
    new_name.segments = env
        .env
        .db
        .lookup_intern_path_data(env.env.source.path)
        .0
        .iter()
        .map(|s| Name {
            provenance: qualified_name.provenance.clone(),
            contents: *s,
        })
        .chain(new_name.segments)
        .collect();
    if let Some(result) = attempt(new_name.clone()) {
        return Some(result);
    }

    /* tracing::debug!(
        "couldn't find {}: {:#?} {:#?}",
        qualified_name.display(env.env.db.up()),
        env.env
            .definitions
            .keys()
            .map(|k| env
                .env
                .db
                .lookup_intern_path_data(*k)
                .0
                .iter()
                .map(|s| env.env.db.lookup_intern_string_data(*s))
                .collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        env.extra_defs
            .keys()
            .map(|k| env
                .env
                .db
                .lookup_intern_path_data(*k)
                .0
                .iter()
                .map(|s| env.env.db.lookup_intern_string_data(*s))
                .collect::<Vec<_>>())
            .collect::<Vec<_>>()
    ); */

    None
}

fn elaborate_universe(env: &ElabEnv, u: &PUniverse) -> Dr<Universe> {
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
                    env.env.db.intern_string_data(text.to_owned()),
                )),
            )),
        },
    }
}
