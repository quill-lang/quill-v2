use fcommon::{Dr, PathData};
use fnodes::{
    basic_nodes::{Name, Provenance},
    definition::{Definition, DefinitionContents},
    expr::{Apply, Expr, ExprContents, MetavariableGenerator},
    inductive::Inductive,
};

use crate::{
    expr::{abstract_nary_pi, abstract_pi, create_nary_application, ExprPrinter},
    typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment},
};

use super::{
    check::PartialInductiveInformation,
    recursor_info::{recursor_info, RecursorInfo, RecursorUniverse},
};

pub fn generate_recursor(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
    info: &PartialInductiveInformation,
) -> Dr<(RecursorInfo, CertifiedDefinition)> {
    recursor_info(env, meta_gen, ind, info)
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
