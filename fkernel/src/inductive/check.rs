use fcommon::{Dr, Label, LabelType, Report, ReportKind};
use fnodes::{
    basic_nodes::{Name, QualifiedName},
    expr::{Expr, ExprContents, Inst, LocalConstant, MetavariableGenerator, Sort},
    inductive::Inductive,
    universe::{Universe, UniverseContents, UniverseVariable},
};

use crate::{
    expr::instantiate,
    typeck::{
        as_sort, check_no_local_or_metavariable, infer_type, to_weak_head_normal_form, Environment,
    },
    universe::{is_nonzero, is_zero},
};

/// Verifies that an inductive type is valid and can be added to the environment.
pub fn check_inductive_type(
    env: &Environment,
    meta_gen: &mut MetavariableGenerator,
    ind: &Inductive,
) -> Dr<PartialInductiveInformation> {
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

        // Ensure that `ind.contents.ty` is type correct.
        infer_type(env, meta_gen, &ind.contents.ty, true).bind(|_| {
            let mut ty = ind.contents.ty.clone();
            to_weak_head_normal_form(env, &mut ty);

            // Unpack the inductive's type as a sequence of `Pi` abstractions.
            // The first `ind.contents.global_params` parameters are pushed into `global_params`,
            // the rest are pushed into `index_params`.
            let mut global_params = Vec::new();
            let mut index_params = Vec::new();
            loop {
                if let ExprContents::Pi(pi) = ty.contents {
                    let local = pi.generate_local(meta_gen);
                    if (global_params.len() as u32) < ind.contents.global_params {
                        // This parameter is a global parameter.
                        global_params.push(local.clone());
                    } else {
                        index_params.push(local.clone());
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
                return Dr::fail(
                    Report::new(
                        ReportKind::Error,
                        env.source,
                        ind.contents.ty.provenance.span().start,
                    )
                    .with_message("the amount of declared global parameters is greater than the amount of parameters to the inductive type")
                    .with_label(Label::new(env.source, ind.contents.ty.provenance.span(), LabelType::Error)
                        .with_message(format!("the type requires {} global parameters but only {} were supplied",
                            ind.contents.global_params, global_params.len()))),
                );
            }

            // The result of applying all the `Pi` abstractions should be a sort.

            as_sort(env, ty).map(|sort| {
                let never_zero = is_nonzero(&sort.0);
                let dependent_elimination = !is_zero(&sort.0);
                PartialInductiveInformation {
                    global_params,
                    index_params,
                    sort,
                    inst,
                    never_zero,
                    dependent_elimination,
                }
            })
        })
    })
}

/// Some information used when creating things to do with inductives, such as recursors.
pub struct PartialInductiveInformation {
    /// Contains exactly `Inductive::contents.global_params` parameters,
    /// which are local constants representing the global parameters for this inductive type.
    pub global_params: Vec<LocalConstant>,
    /// Contains the remaining parameters which are not global parameters.
    /// These can be thought of as indexing particular types with the same set of global parameters.
    pub index_params: Vec<LocalConstant>,
    /// The type yielded after all parameters have been applied to the inductive type.
    pub sort: Sort,
    /// An `Inst` node which will instantiate the type of the inductive, with the given universe parameters.
    pub inst: Inst,
    /// True if the field `sort` is never the zero universe.
    pub never_zero: bool,
    /// True if we need to perform dependent elimination in the recursor.
    /// This means that the type former C can depend on the value of the inductive in question.
    pub dependent_elimination: bool,
}
