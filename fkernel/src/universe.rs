//! Manipulates chains of successor universes.

use std::ops::DerefMut;

use fnodes::{basic_nodes::Provenance, universe::*};

/// Factors out the outermost sequence of [`UniverseSucc`] instances.
/// If the input is `u + k` where `k` is an integer, we remove the `+ k` from the input and return `k`.
fn to_universe_with_offset(u: &mut Universe) -> UniverseLevel {
    if let UniverseContents::UniverseSucc(UniverseSucc(inner)) = &mut u.contents {
        let result = to_universe_with_offset(inner);
        let inner = std::mem::replace(
            inner.deref_mut(),
            Universe::new_synthetic(UniverseContents::UniverseZero),
        );
        *u = inner;
        result + 1
    } else {
        0
    }
}

/// Reverses [`to_universe_with_offset`] by adding iterated `+ 1` operations to this universe.
fn from_universe_with_offset(
    u: &mut Universe,
    levels_to_raise: UniverseLevel,
    new_provenance: Provenance,
) {
    let mut contents = std::mem::replace(&mut u.contents, UniverseContents::UniverseZero);
    for _ in 0..levels_to_raise {
        contents = UniverseContents::UniverseSucc(UniverseSucc(Box::new(Universe {
            provenance: new_provenance.clone(),
            contents,
        })));
    }
    u.contents = contents;
}

/// Returns true if this universe is definitely not the zero universe, `Prop`.
/// It is possible for [`is_zero`] and [`is_nonzero`] to both be false.
fn is_nonzero(u: &Universe) -> bool {
    match &u.contents {
        UniverseContents::UniverseZero => false,
        UniverseContents::UniverseVariable(_) => false,
        UniverseContents::UniverseSucc(_) => true,
        UniverseContents::UniverseMax(max) => is_nonzero(&max.left) || is_nonzero(&max.right),
        // Even if the left hand side of an `imax` is nonzero, the result is still zero if the right hand side is.
        UniverseContents::UniverseImpredicativeMax(imax) => is_nonzero(&imax.right),
        UniverseContents::Metauniverse(_) => false,
    }
}

/// Returns true if this universe is definitely zero.
/// It is possible for [`is_zero`] and [`is_nonzero`] to both be false.
fn is_zero(u: &Universe) -> bool {
    matches!(&u.contents, UniverseContents::UniverseZero)
}

/// Converts a universe to an equivalent, simpler, form.
pub fn normalise_universe(u: &mut Universe) {
    // First, factor out the outermost `+ k` chain.
    let provenance = u.provenance.clone();
    let levels = to_universe_with_offset(u);
    match &mut u.contents {
        UniverseContents::UniverseZero => {}
        UniverseContents::UniverseVariable(_) => {}
        UniverseContents::UniverseSucc(_) => {
            unreachable!("should have already factored out succ chain")
        }
        UniverseContents::UniverseMax(max) => {
            let max = std::mem::replace(
                max,
                UniverseMax {
                    left: Box::new(Universe::new_synthetic(UniverseContents::UniverseZero)),
                    right: Box::new(Universe::new_synthetic(UniverseContents::UniverseZero)),
                },
            );
            *u = normalise_max_chain(max);
        }
        UniverseContents::UniverseImpredicativeMax(imax) => {
            normalise_universe(&mut *imax.left);
            normalise_universe(&mut *imax.right);
            // We now need to check if we can perform a simplification on this `imax` operation.
            let imax = std::mem::replace(
                imax,
                UniverseImpredicativeMax {
                    left: Box::new(Universe::new_synthetic(UniverseContents::UniverseZero)),
                    right: Box::new(Universe::new_synthetic(UniverseContents::UniverseZero)),
                },
            );
            *u = normalise_imax(imax);
        }
        UniverseContents::Metauniverse(_) => {}
    }
    from_universe_with_offset(u, levels, provenance);
}

fn normalise_imax(imax: UniverseImpredicativeMax) -> Universe {
    if is_nonzero(&imax.right) {
        // This is a regular max expression.
        normalise_max_chain(UniverseMax {
            left: imax.left,
            right: imax.right,
        })
    } else if is_zero(&imax.left) || is_zero(&imax.right) {
        // If the left parameter is zero, the result is the right parameter.
        // If the right parameter is zero, then the result is zero, which is the right parameter.
        *imax.right
    } else if imax.left.eq_ignoring_provenance(&imax.right) {
        // If the two parameters are equal we can just take one of them as the result.
        *imax.left
    } else {
        // Couldn't simplify.
        Universe::new_synthetic(UniverseContents::UniverseImpredicativeMax(imax))
    }
}

fn normalise_max_chain(max: UniverseMax) -> Universe {
    // Flatten out nested invocations of `max`, normalise all parameters, and flatten again.
    let mut args = collect_max_args(max)
        .into_iter()
        .flat_map(|mut arg| {
            normalise_universe(&mut arg);
            if let UniverseContents::UniverseMax(inner) = arg.contents {
                collect_max_args(inner)
            } else {
                vec![arg]
            }
        })
        .collect::<Vec<_>>();
    // Now, we sort the arguments so that easily comparable arguments are grouped.
    args.sort_by_key(|arg| match &arg.contents {
        UniverseContents::UniverseZero => 0,
        UniverseContents::UniverseSucc(_) => 1,
        UniverseContents::UniverseMax(_) => 2,
        UniverseContents::UniverseImpredicativeMax(_) => 3,
        UniverseContents::UniverseVariable(_) => 4,
        UniverseContents::Metauniverse(_) => 5,
    });
    // Collect the chain of arguments together.
    // We reverse the iterator so this behaves like a right-facing fold.
    args.into_iter()
        .rev()
        .reduce(|right, left| {
            normalise_max(UniverseMax {
                left: Box::new(left),
                right: Box::new(right),
            })
        })
        .expect("args should be nonempty")
}

fn collect_max_args(max: UniverseMax) -> Vec<Universe> {
    let mut left = if let UniverseContents::UniverseMax(inner) = max.left.contents {
        collect_max_args(inner)
    } else {
        vec![*max.left]
    };
    let right = if let UniverseContents::UniverseMax(inner) = max.right.contents {
        collect_max_args(inner)
    } else {
        vec![*max.right]
    };
    left.extend(right);
    left
}

fn normalise_max(mut max: UniverseMax) -> Universe {
    if let (Some(left), Some(right)) = (max.left.to_explicit_universe(), max.right.to_explicit_universe()) {
        // We can compare the universes directly because we know their values.
        if left >= right {
            *max.left
        } else {
            *max.right
        }
    } else if is_zero(&max.left) {
        // If the left parameter is zero, the result is the right parameter.
        *max.right
    } else if is_zero(&max.right) {
        // If the right parameter is zero, the result is the left parameter.
        *max.left
    } else if max.left.eq_ignoring_provenance(&max.right) {
        // If the two parameters are equal we can just take one of them as the result.
        *max.left
    } else if let UniverseContents::UniverseMax(left_max) = &max.left.contents
        && (left_max.left.eq_ignoring_provenance(&max.right) || left_max.right.eq_ignoring_provenance(&max.right)) {
        // The result of `max (max a b) a` or `max (max a b) b` is `max a b`.
        *max.left
    } else if let UniverseContents::UniverseMax(right_max) = &max.right.contents
        && (right_max.left.eq_ignoring_provenance(&max.left) || right_max.right.eq_ignoring_provenance(&max.left)) {
        // The result of `max a (max a b)` or `max b (max a b)` is `max a b`.
        *max.right
    } else {
        // Try to factor out `+ k` chains from the left and right arguments.
        let left_provenance = max.left.provenance.clone();
        let right_provenance = max.right.provenance.clone();
        let left_levels = to_universe_with_offset(max.left.deref_mut());
        let right_levels = to_universe_with_offset(max.right.deref_mut());
        if max.left.eq_ignoring_provenance(&max.right) {
            // We can now compare levels directly.
            if left_levels >= right_levels {
                from_universe_with_offset(&mut max.left, left_levels, left_provenance);
                *max.left
            } else {
                from_universe_with_offset(&mut max.right, right_levels, right_provenance);
                *max.right
            }
        } else {
            // Couldn't simplify. Revert the `+ k` chains for now.
            from_universe_with_offset(&mut max.left, left_levels, left_provenance);
            from_universe_with_offset(&mut max.right, right_levels, right_provenance);
            Universe::new_synthetic(UniverseContents::UniverseMax(max))
        }
    }
}

enum ReplaceResult {
    /// The expression should not be replaced.
    Skip,
    /// The expression should be replaced with the given value.
    ReplaceWith(Universe),
}

fn replace_in_universe(u: &mut Universe, replace_fn: impl Clone + Fn(&Universe) -> ReplaceResult) {
    match replace_fn.clone()(u) {
        ReplaceResult::Skip => match &mut u.contents {
            UniverseContents::UniverseZero => {}
            UniverseContents::UniverseVariable(_) => {}
            UniverseContents::UniverseSucc(inner) => replace_in_universe(&mut inner.0, replace_fn),
            UniverseContents::UniverseMax(max) => {
                replace_in_universe(&mut max.left, replace_fn.clone());
                replace_in_universe(&mut max.right, replace_fn);
            }
            UniverseContents::UniverseImpredicativeMax(imax) => {
                replace_in_universe(&mut imax.left, replace_fn.clone());
                replace_in_universe(&mut imax.right, replace_fn);
            }
            UniverseContents::Metauniverse(_) => {}
        },
        ReplaceResult::ReplaceWith(replacement) => *u = replacement,
    }
}

/// Replace the given universe variable with the provided replacement.
pub fn instantiate_universe(u: &mut Universe, var: UniverseVariable, replacement: &Universe) {
    replace_in_universe(u, |inner| match &inner.contents {
        UniverseContents::UniverseVariable(inner_var) => {
            if *inner_var == var {
                ReplaceResult::ReplaceWith(replacement.clone())
            } else {
                ReplaceResult::Skip
            }
        }
        _ => ReplaceResult::Skip,
    })
}

/// Replace the given metauniverse with the provided replacement.
pub fn instantiate_metauniverse(u: &mut Universe, meta: Metauniverse, replacement: &Universe) {
    replace_in_universe(u, |inner| match &inner.contents {
        UniverseContents::Metauniverse(inner_meta) => {
            if *inner_meta == meta {
                ReplaceResult::ReplaceWith(replacement.clone())
            } else {
                ReplaceResult::Skip
            }
        }
        _ => ReplaceResult::Skip,
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::test_db::*;
    use fcommon::Intern;
    use fcommon::SourceType;
    use fnodes::expr::ExprContents;
    use fnodes::expr::Sort;
    use fnodes::universe::Universe;
    use fnodes::universe::UniverseContents;
    use fnodes::{module::Module, SexprParser};

    #[test]
    fn test_normalise_universe() {
        let contents = "
        (module
            ()
            (def univ ()
                (sort (univimax (univsucc (univzero)) (univzero)))
            )
            (def univ_result ()
                (sort (univzero))
            )
            (def univ2 ()
                (sort (univmax (univsucc (univzero)) (univmax (univmax (univmeta 0) (univzero)) (univsucc (univzero)))))
            )
            (def univ2_result ()
                (sort (univmax (univsucc (univzero)) (univmeta 0)))
            )
        )
        ";
        let (db, source) = database_with_file(vec!["test", "sexpr"], SourceType::Feather, contents);
        let module: Arc<Module> = db.module_from_feather_source(source).unwrap();
        for test in ["univ", "univ2"] {
            let mut expr = module
                .definition(db.intern_string_data(test.to_string()))
                .unwrap()
                .contents
                .ty
                .clone();
            let mut result = module
                .definition(db.intern_string_data(format!("{}_result", test)))
                .unwrap()
                .contents
                .ty
                .clone();
            if let ExprContents::Sort(Sort(sort)) = &mut expr.contents {
                if let ExprContents::Sort(Sort(result)) = &mut result.contents {
                    normalise_universe(sort);
                    if !sort.eq_ignoring_provenance(result) {
                        panic!("mismatch:\n{:?}\n{:?}", sort, result);
                    }
                } else {
                    unreachable!()
                }
            } else {
                unreachable!()
            }
        }
    }
}
