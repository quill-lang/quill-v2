use fcommon::{Dr, PathData};
use fnodes::{
    basic_nodes::Name,
    definition::{Definition, DefinitionContents},
    expr::MetavariableGenerator,
    inductive::Inductive,
};

use crate::typeck::{self, CertifiedDefinition, DefinitionOrigin, Environment};

mod check;
mod check_intro_rule;
mod comp_rule;
mod recursor;
mod recursor_info;

use self::{
    check_intro_rule::check_intro_rule,
    comp_rule::{generate_computation_rules, ComputationRule},
    recursor::generate_recursor,
    recursor_info::RecursorUniverse,
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

                // Form the recursor.
                let recursor = generate_recursor(&env, &mut meta_gen, ind, &info);
                if let Some((rec_info, recursor_def)) = recursor.value() {
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
                    recursor.bind(move |(rec_info, recursor)| {
                        comp_rules.map(move |computation_rules| {
                            (intro_rules, recursor, computation_rules)
                        })
                    })
                } else {
                    recursor.map(|_| unreachable!())
                }
            })
            .map(
                move |(intro_rules, recursor, computation_rules)| CertifiedInductiveInformation {
                    inductive: CertifiedInductive {
                        inductive: ind.clone(),
                        computation_rules,
                    },
                    type_declaration,
                    intro_rules,
                    recursor,
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
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct CertifiedInductive {
    /// The inductive data type we have certified.
    inductive: Inductive,
    /// The reduction rules used for computing applications of the recursor.
    computation_rules: Vec<ComputationRule>,
}

impl CertifiedInductive {
    pub fn inductive(&self) -> &Inductive {
        &self.inductive
    }

    pub fn computation_rules(&self) -> &[ComputationRule] {
        self.computation_rules.as_ref()
    }
}
