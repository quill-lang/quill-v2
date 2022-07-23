use fcommon::{Dr, PathData};
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    definition::{Definition, DefinitionContents},
    expr::{
        Apply, BinderAnnotation, Delta, Expr, ExprContents, LocalConstant, MetavariableGenerator,
        Region,
    },
    inductive::Inductive,
};

use crate::{
    expr::{abstract_nary_pi, abstract_pi, create_nary_application, pi_args, ExprPrinter},
    typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment},
};

use super::{
    check::PartialInductiveInformation,
    recursor_info::{recursor_info, RecursorForm, RecursorInfo, RecursorUniverse},
};

pub fn generate_recursor(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<(RecursorInfo, CertifiedDefinition)> {
    recursor_info(env, meta_gen, ind, info, RecursorForm::Owned)
        .bind(|rec_info| {
            let def = generate_recursor_core(env, ind, info, &rec_info);
            let mut print = ExprPrinter::new(env.db);
            tracing::debug!("eliminator has type {}", print.print(&def.contents.ty));

            let mut env = env.clone();

            // Add the universe parameter created for the type former if applicable.
            let mut universe_variables = env.universe_variables.to_owned();
            match rec_info.recursor_universe {
                RecursorUniverse::Prop => {}
                RecursorUniverse::Parameter(param) => {
                    let new_universe_parameter = Name {
                        provenance: ind.provenance.clone(),
                        contents: param,
                    };
                    universe_variables.insert(0, new_universe_parameter);
                }
            };
            env.universe_variables = &universe_variables;

            typeck::check(
                &env,
                &def,
                DefinitionOrigin::Recursor {
                    inductive: env.db.intern_path_data(PathData(
                        env.db
                            .lookup_intern_path_data(env.source.path)
                            .0
                            .into_iter()
                            .chain(std::iter::once(ind.contents.name.contents))
                            .collect(),
                    )),
                },
            )
            .map(|def| (rec_info, def))
        })
        .map_reports(|report| {
            report.with_note(format!(
                "error raised while creating the recursor for type {}",
                env.db.lookup_intern_string_data(ind.contents.name.contents)
            ))
        })
}

fn generate_recursor_core(
    env: &Environment,
    ind: &Inductive,
    info: &PartialInductiveInformation,
    rec_info: &RecursorInfo,
) -> Definition {
    let mut type_former_application = create_nary_application(
        Expr::new_synthetic(ExprContents::LocalConstant(rec_info.type_former.clone())),
        info.index_params
            .iter()
            .map(|local| Expr::new_synthetic(ExprContents::LocalConstant(local.clone()))),
        &Provenance::Synthetic,
    );
    if info.dependent_elimination {
        type_former_application = Expr::new_synthetic(ExprContents::Apply(Apply {
            function: Box::new(type_former_application),
            argument: Box::new(Expr::new_synthetic(ExprContents::LocalConstant(
                rec_info.major_premise.clone(),
            ))),
        }))
    }

    // Create the type for the eliminator.
    let mut eliminator_type = abstract_nary_pi(
        info.index_params.iter().cloned(),
        Expr::new_synthetic(ExprContents::Pi(abstract_pi(
            rec_info.major_premise.clone(),
            type_former_application,
        ))),
        &Provenance::Synthetic,
    );

    // Abstract the introduction rules.
    eliminator_type = abstract_nary_pi(
        rec_info.minor_premises.iter().cloned(),
        eliminator_type,
        &Provenance::Synthetic,
    );

    // Abstract the type former.
    eliminator_type = Expr::new_synthetic(ExprContents::Pi(abstract_pi(
        rec_info.type_former.clone(),
        eliminator_type,
    )));

    // Abstract the global parameters.
    eliminator_type = abstract_nary_pi(
        info.global_params.iter().cloned(),
        eliminator_type,
        &Provenance::Synthetic,
    );

    let eliminator_universe = match rec_info.recursor_universe {
        RecursorUniverse::Prop => Vec::new(),
        RecursorUniverse::Parameter(param) => vec![Name {
            provenance: ind.provenance.clone(),
            contents: param,
        }],
    };

    Definition {
        provenance: ind.provenance.clone(),
        contents: DefinitionContents {
            name: Name {
                contents: env.db.intern_string_data(format!(
                    "{}.rec",
                    env.db.lookup_intern_string_data(ind.contents.name.contents)
                )),
                provenance: ind.contents.name.provenance.clone(),
            },
            universe_params: eliminator_universe
                .into_iter()
                .chain(ind.contents.universe_params.clone())
                .collect(),
            ty: eliminator_type,
            expr: None,
        },
    }
}

pub fn generate_borrowed_recursor(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    squashed: &Inductive,
    squash_function: &CertifiedDefinition,
    info: &PartialInductiveInformation,
) -> Dr<(RecursorInfo, CertifiedDefinition)> {
    let region = pi_args(&squashed.contents.ty, meta_gen)
        .get(0)
        .cloned()
        .unwrap_or_else(|| {
            // If there was no region parameter (e.g. if there are no fields that need to be squashed), we need to make our own region parameter.
            // TODO: There are cases where the squashed type does not need a region parameter, but has other parameters, so this is not correct.
            LocalConstant {
                name: Name {
                    provenance: Provenance::Synthetic,
                    contents: env.db.intern_string_data("r".to_string()),
                },
                metavariable: meta_gen.gen(Expr::new_synthetic(ExprContents::Region(Region))),
                binder_annotation: BinderAnnotation::Explicit,
            }
        });

    recursor_info(
        env,
        meta_gen,
        ind,
        info,
        RecursorForm::Borrowed {
            region: &region,
            squashed_type: &QualifiedName {
                provenance: ind.contents.name.provenance.clone(),
                segments: env
                    .db
                    .lookup_intern_path_data(env.source.path)
                    .0
                    .into_iter()
                    .map(|s| Name {
                        provenance: ind.contents.name.provenance.clone(),
                        contents: s,
                    })
                    .chain(std::iter::once(squashed.contents.name.clone()))
                    .collect(),
            },
            squash: &QualifiedName {
                provenance: ind.contents.name.provenance.clone(),
                segments: env
                    .db
                    .lookup_intern_path_data(env.source.path)
                    .0
                    .into_iter()
                    .map(|s| Name {
                        provenance: ind.contents.name.provenance.clone(),
                        contents: s,
                    })
                    .chain(std::iter::once(squash_function.def().contents.name.clone()))
                    .collect(),
            },
        },
    )
    .bind(|rec_info| {
        let def = generate_recursor_core(env, ind, info, &rec_info);
        let mut print = ExprPrinter::new(env.db);
        tracing::debug!(
            "borrowed eliminator has type {}",
            print.print(&def.contents.ty)
        );

        let mut env = env.clone();

        // Add the universe parameter created for the type former if applicable.
        let mut universe_variables = env.universe_variables.to_owned();
        match rec_info.recursor_universe {
            RecursorUniverse::Prop => {}
            RecursorUniverse::Parameter(param) => {
                let new_universe_parameter = Name {
                    provenance: ind.provenance.clone(),
                    contents: param,
                };
                universe_variables.insert(0, new_universe_parameter);
            }
        };
        env.universe_variables = &universe_variables;

        typeck::check(
            &env,
            &def,
            DefinitionOrigin::Recursor {
                inductive: env.db.intern_path_data(PathData(
                    env.db
                        .lookup_intern_path_data(env.source.path)
                        .0
                        .into_iter()
                        .chain(std::iter::once(ind.contents.name.contents))
                        .collect(),
                )),
            },
        )
        .map(|def| (rec_info, def))
    })
    .map_reports(|report| {
        report.with_note(format!(
            "error raised while creating the borrowed form of the recursor for type {}",
            env.db.lookup_intern_string_data(ind.contents.name.contents)
        ))
    })
}
