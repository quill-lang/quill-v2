use fcommon::Dr;
use fnodes::{
    basic_nodes::{Name, QualifiedName},
    expr::{Expr, ExprContents, Inst, MetavariableGenerator, Sort},
    inductive::Inductive,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::instantiate,
    typeck::{
        as_sort, check_no_local_or_metavariable, infer_type, to_weak_head_normal_form, Environment,
    },
    universe::is_nonzero,
};

/// Verifies that an inductive type is valid and can be added to the environment.
pub fn check_inductive_type(env: &Environment, ind: &Inductive) -> Dr<PartialInductiveInformation> {
    check_no_local_or_metavariable(env, &ind.contents.ty).bind(|()| {
        let inst = Inst {
            name: QualifiedName {
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
                    .chain(std::iter::once(ind.contents.name.clone()))
                    .collect(),
            },
            universes: ind
                .contents
                .universe_params
                .iter()
                .map(|univ| {
                    Universe::new_with_provenance(
                        &univ.provenance,
                        UniverseContents::UniverseVariable(UniverseVariable(univ.contents)),
                    )
                })
                .collect(),
        };

        // Since we have no metavariables in the inductive's type,
        // we can initialise the metavariable generator with any value.
        let mut meta_gen = MetavariableGenerator::new(None);

        // Ensure that `ind.contents.ty` is type correct.
        infer_type(env, &mut meta_gen, &ind.contents.ty, true).bind(|_| {
            let mut ty = ind.contents.ty.clone();
            to_weak_head_normal_form(env, &mut ty);

            // Unpack the inductive's type as a sequence of `Pi` abstractions.
            // The first `ind.contents.global_params` parameters are pushed into `global_params`,
            // the rest are pushed into `index_params`.
            let mut global_params = Vec::new();
            let mut index_params = Vec::new();
            loop {
                if let ExprContents::Pi(pi) = ty.contents {
                    let local = pi.generate_local(&mut meta_gen);
                    if (global_params.len() as u32) < ind.contents.global_params {
                        // This parameter is a global parameter.
                        global_params.push(*pi.parameter_ty);
                    } else {
                        index_params.push(*pi.parameter_ty);
                    }
                    ty = *pi.result;
                    instantiate(
                        &mut ty,
                        &Expr::new_synthetic(ExprContents::LocalConstant(local)),
                    );
                    to_weak_head_normal_form(env, &mut ty);
                } else {
                    break;
                }
            }

            // By now, we should have supplied exactly the correct amount of `global_params`.
            if (global_params.len() as u32) != ind.contents.global_params {
                return Dr::fail(todo!());
            }

            // The result of applying all the `Pi` abstractions should be a sort.
            as_sort(env, ty).map(|sort| PartialInductiveInformation {
                global_params,
                index_params,
                sort,
                never_zero: is_nonzero(&sort.0),
                inst,
            })
        })
    })
}

/// Some information used when creating things to do with inductives, such as recursors.
#[derive(Debug)]
pub struct PartialInductiveInformation {
    /// Contains exactly `Inductive::contents.global_params` parameters,
    /// which are the global parameters for this inductive type.
    global_params: Vec<Expr>,
    index_params: Vec<Expr>,
    /// The type yielded after all parameters have been applied to the inductive type.
    sort: Sort,
    /// True if the field `sort` is never the zero universe.
    never_zero: bool,
    /// An `Inst` node which will instantiate the type of the inductive, with the given universe parameters.
    inst: Inst,
}
