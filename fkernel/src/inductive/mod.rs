use fcommon::{Dr, PathData};
use fnodes::{
    basic_nodes::{Name, Provenance},
    definition::{Definition, DefinitionContents},
    expr::{BinderAnnotation, Expr, ExprContents, LocalConstant, MetavariableGenerator, Region},
    inductive::Inductive,
};

use crate::{
    expr::ExprPrinter,
    typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment},
};

mod check;
mod check_intro_rule;
mod comp_rule;
mod recursor;
mod recursor_info;
mod squash_rule;
mod squash_type;

use self::{
    check_intro_rule::check_intro_rule,
    comp_rule::{generate_computation_rules, ComputationRule},
    recursor::{generate_borrowed_recursor, generate_recursor},
    recursor_info::RecursorUniverse,
    squash_rule::{generate_squash_function, generate_squash_rules},
    squash_type::squashed_type,
};

/// Verifies that an inductive type is valid and can be added to the environment.
/// Takes ownership of the environment so we can add definitions to it while performing inference.
pub fn check_inductive_type(
    env: Environment,
    ind: &Inductive,
) -> Dr<CertifiedInductiveInformation> {
    // We are going to assert that we have no metavariables in the inductive's type,
    // so we can initialise the metavariable generator with any value.
    let mut meta_gen = MetavariableGenerator::new(None);

    check::check_inductive_type(&env, &mut meta_gen, ind).bind(move |info| {
        let type_declaration = Definition {
            provenance: ind.contents.name.provenance.clone(),
            contents: DefinitionContents {
                name: ind.contents.name.clone(),
                universe_params: ind.contents.universe_params.clone(),
                ty: ind.contents.ty.clone(),
                expr: None,
            },
        };
        typeck::check(
            &env,
            &type_declaration,
            DefinitionOrigin::TypeDeclaration {
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
        .bind(move |type_declaration| {
            // Shorten the lifetime parameter on `env` to just this block.
            let mut env: Environment<'_> = env;
            {
                // Add the type declaration to the environment.
                let mut new_path_data = env.db.lookup_intern_path_data(env.source.path);
                new_path_data
                    .0
                    .push(type_declaration.def().contents.name.contents);
                let path = env.db.intern_path_data(new_path_data);
                env.definitions.insert(path, &type_declaration);
            }

            Dr::sequence(
                ind.contents.intro_rules.iter().map(|intro_rule| {
                    check_intro_rule(&env, &mut meta_gen, ind, intro_rule, &info)
                }),
            )
            .bind(move |intro_rules| {
                // Shorten the lifetime parameter on `env` again.
                let mut env: Environment<'_> = env;
                for intro_rule in &intro_rules {
                    // Add the intro rules to the environment.
                    let mut new_path_data = env.db.lookup_intern_path_data(env.source.path);
                    new_path_data
                        .0
                        .push(intro_rule.def().contents.name.contents);
                    let path = env.db.intern_path_data(new_path_data);
                    env.definitions.insert(path, intro_rule);
                }

                // Generate the squashed type.
                let squashed = squashed_type(&env, &mut meta_gen, ind);

                // Recursion: taking the squashed type is idempotent, so this recurses only at most once.
                let squashed_checked = squashed
                    .as_ref()
                    .map(|squashed| check_inductive_type(env.clone(), squashed));
                if let Some(squashed_checked) = &squashed_checked {
                    if let Some(squashed_checked) = &squashed_checked.value() {
                        // Add the squashed type into the environment.
                        env.definitions.insert(
                            env.db.intern_path_data({
                                let mut path = env.db.lookup_intern_path_data(env.source.path);
                                path.0.push(
                                    squashed_checked.inductive.inductive.contents.name.contents,
                                );
                                path
                            }),
                            &squashed_checked.type_declaration,
                        );
                    }
                }

                let squash_function = generate_squash_function(
                    &env,
                    &mut meta_gen,
                    ind,
                    squashed.as_ref().unwrap_or(ind),
                );

                if let Some(squash_function) = &squash_function.value() {
                    // Add the squash function into the environment.
                    env.definitions.insert(
                        env.db.intern_path_data({
                            let mut path = env.db.lookup_intern_path_data(env.source.path);
                            path.0.push(squash_function.def().contents.name.contents);
                            path
                        }),
                        squash_function,
                    );
                }

                let squash_rules = generate_squash_rules(
                    &env,
                    &mut meta_gen,
                    ind,
                    squashed.as_ref().unwrap_or(ind),
                );

                if let Some(squash_function_value) = squash_function.value() {
                    // Form the recursors, both in owned and borrowed form.
                    let recursor =
                        generate_recursor(&env, &mut meta_gen, ind, &info).bind(|recursor| {
                            generate_borrowed_recursor(
                                &env,
                                &mut meta_gen,
                                ind,
                                squashed.as_ref().unwrap_or(ind),
                                squash_function_value,
                                &info,
                            )
                            .map(|borrowed_recursor| (recursor, borrowed_recursor))
                        });
                    if let Some((
                        (rec_info, recursor_def),
                        (borrowed_rec_info, borrowed_recursor_def),
                    )) = recursor.value()
                    {
                        // Put the recursor in the environment.
                        // This shouldn't need to be outside a `bind`, this is just lifetime hacking.
                        let mut new_path_data = env.db.lookup_intern_path_data(env.source.path);
                        new_path_data
                            .0
                            .push(recursor_def.def().contents.name.contents);
                        let path = env.db.intern_path_data(new_path_data);
                        env.definitions.insert(path, recursor_def);

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

                        // Generate the computation rules for the recursor.
                        let comp_rules =
                            generate_computation_rules(&env, &mut meta_gen, ind, &info, rec_info);

                        squashed_checked
                            .map(|dr| dr.map(Some))
                            .unwrap_or_else(|| Dr::ok(None))
                            .bind(move |squashed_type| {
                                squash_function.bind(|squash_function| {
                                    recursor.bind(
                                        move |(
                                            (rec_info, recursor_def),
                                            (borrowed_rec_info, borrowed_recursor_def),
                                        )| {
                                            comp_rules.map(move |computation_rules| {
                                                (
                                                    intro_rules,
                                                    squashed_type,
                                                    recursor_def,
                                                    computation_rules,
                                                    squash_function,
                                                    squash_rules,
                                                )
                                            })
                                        },
                                    )
                                })
                            })
                    } else {
                        recursor.map(|_| unreachable!())
                    }
                } else {
                    squashed_checked
                        .map(|dr| dr.map(Some))
                        .unwrap_or_else(|| Dr::ok(None))
                        .bind(|_| squash_function.map(|_| unreachable!()))
                }
            })
            .map(
                move |(
                    intro_rules,
                    squashed_type,
                    recursor,
                    computation_rules,
                    squash,
                    squash_rules,
                )| {
                    CertifiedInductiveInformation {
                        inductive: CertifiedInductive {
                            inductive: ind.clone(),
                            computation_rules,
                            squash_rules,
                        },
                        type_declaration,
                        intro_rules,
                        recursor,
                        squashed_type: squashed_type.map(Box::new),
                        squash,
                    }
                },
            )
        })
    })
}

#[derive(Debug)]
pub struct CertifiedInductiveInformation {
    /// The certified inductive data type we are providing information for.
    pub inductive: CertifiedInductive,
    /// A definition with no body which constructs the type itself.
    pub type_declaration: CertifiedDefinition,
    /// Definitions with no body representing the introduction rules.
    pub intro_rules: Vec<CertifiedDefinition>,
    /// The recursor for this inductive data type.
    pub recursor: CertifiedDefinition,
    /// If this has a squashed type, it is stored here.
    pub squashed_type: Option<Box<CertifiedInductiveInformation>>,
    /// The squash function for this inductive data type.
    pub squash: CertifiedDefinition,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct CertifiedInductive {
    /// The inductive data type we have certified.
    inductive: Inductive,
    /// The reduction rules used for computing applications of the recursor.
    computation_rules: Vec<ComputationRule>,
    /// The reduction rules used for computing applications of the squash function.
    squash_rules: Vec<ComputationRule>,
}

impl CertifiedInductive {
    pub fn inductive(&self) -> &Inductive {
        &self.inductive
    }

    pub fn computation_rules(&self) -> &[ComputationRule] {
        self.computation_rules.as_ref()
    }

    pub fn squash_rules(&self) -> &[ComputationRule] {
        self.squash_rules.as_ref()
    }
}
