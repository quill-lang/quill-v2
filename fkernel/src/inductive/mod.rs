use fcommon::Dr;
use fnodes::{
    definition::{Definition, DefinitionContents},
    expr::MetavariableGenerator,
    inductive::Inductive,
};

use crate::typeck::{self, CertifiedDefinition, Environment};

mod check;
mod check_intro_rule;

use self::{check::PartialInductiveInformation, check_intro_rule::check_intro_rule};

/// Verifies that an inductive type is valid and can be added to the environment.
/// Takes ownership of the environment so we can add definitions to it while performing inference.
pub(crate) fn check_inductive_type(
    mut env: Environment,
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
        typeck::check(&env, &type_declaration).bind(move |type_declaration| {
            // Shorten the lifetime parameter on `env` to just this block.
            let mut env: Environment<'_> = env;
            let mut new_path_data = env.db.lookup_intern_path_data(env.source.path);
            new_path_data
                .0
                .push(type_declaration.def().contents.name.contents);
            let path = env.db.intern_path_data(new_path_data);
            env.definitions.insert(path, &type_declaration);

            let intro_rules =
                Dr::sequence(ind.contents.intro_rules.iter().map(|intro_rule| {
                    check_intro_rule(&env, &mut meta_gen, ind, intro_rule, &info)
                }));

            intro_rules.map(|_| CertifiedInductiveInformation {
                inductive: CertifiedInductive {
                    inductive: ind.clone(),
                },
                type_declaration: type_declaration.clone(),
            })
        })
    })
}

#[derive(Debug)]
pub(crate) struct CertifiedInductiveInformation {
    /// The certified inductive data type we are providing information for.
    pub inductive: CertifiedInductive,
    /// A definition with no body which constructs the type itself.
    pub type_declaration: CertifiedDefinition,
}

#[derive(Debug)]
pub struct CertifiedInductive {
    /// The inductive data type we have certified.
    inductive: Inductive,
}

impl CertifiedInductive {
    pub fn inductive(&self) -> &Inductive {
        &self.inductive
    }
}
