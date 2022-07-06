use std::cmp::Ordering;

use fcommon::{Dr, Label, LabelType, Report, ReportKind};
use fnodes::{
    basic_nodes::{DeBruijnIndex, Provenance},
    expr::*,
    universe::{Universe, UniverseContents},
};

use crate::{expr::instantiate, universe::normalise_universe};

use super::{
    env::Environment,
    infer::infer_type_core,
    unfold::{head_definition_height, unfold_definition},
    whnf::to_weak_head_normal_form,
};

/// Returns true if the two expressions are definitionally equal.
/// This may return an error if the expressions were not type correct.
pub fn definitionally_equal<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Expr,
    right: &Expr,
) -> Dr<bool> {
    match definitionally_equal_core(env, meta_gen, left, right) {
        Ok(result) => Dr::ok(result),
        Err(err) => Dr::fail(err(Report::new(
            ReportKind::Error,
            env.source,
            std::cmp::min(left.provenance.span().start, right.provenance.span().start),
        )
        .with_label(
            Label::new(env.source, left.provenance.span(), LabelType::Note).with_message(
                "error was raised trying to check whether this expression was definitionally equal to...",
            ).with_priority(-100),
        ).with_label(
            Label::new(env.source, right.provenance.span(), LabelType::Note).with_message(
                "...this other expression",
            ).with_priority(-101),
        ))),
    }
}

/// Returns true if the two expressions are definitionally equal.
pub(in crate::typeck) fn definitionally_equal_core<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Expr,
    right: &Expr,
) -> Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>> {
    // Start by reducing to weak head normal form.
    let mut left = left.clone();
    let mut right = right.clone();

    to_weak_head_normal_form(env, &mut left);
    to_weak_head_normal_form(env, &mut right);

    // Test for simple cases first.
    if let Some(result) = quick_definitionally_equal(env, meta_gen, &left, &right) {
        return result;
    }

    // Test for equality based on proof irrelevance.
    if equal_propositions(env, meta_gen, &left, &right)? {
        return Ok(true);
    }

    // Test for equality by performing delta reduction on `left` and `right`.
    // After invoking this, `left` and `right` should be in weak head normal form.
    if let Some(result) = lazy_delta_reduction(env, meta_gen, &mut left, &mut right) {
        return result;
    }

    // Now test all the other cases.
    match (&left.contents, &right.contents) {
        (ExprContents::Inst(left), ExprContents::Inst(right)) => {
            // Test if the two expressions are equal constants.
            if left.universes.len() == right.universes.len()
                && left.universes.iter().zip(&right.universes).all(
                    |(left_universe, right_universe)| {
                        universe_definitionally_equal(left_universe, right_universe)
                    },
                )
            {
                return Ok(true);
            }
        }
        (ExprContents::LocalConstant(left), ExprContents::LocalConstant(right)) => {
            // Test if the two expressions are equal local constants.
            if left.name.contents == right.name.contents {
                return Ok(true);
            }
        }
        (ExprContents::Apply(left), ExprContents::Apply(right)) => {
            // Test if the two expressions are applications of the same function with the same arguments.
            if definitionally_equal_core(env, meta_gen, &left.function, &right.function)?
                && definitionally_equal_core(env, meta_gen, &left.argument, &right.argument)?
            {
                return Ok(true);
            }
        }
        (ExprContents::Lambda(lambda), _) => {
            if !matches!(&right.contents, ExprContents::Lambda(_)) {
                // Test if the we can eta-expand the right expression into the form of the left lambda.
                if let Some(result) =
                    try_eta_expansion(env, meta_gen, lambda, &left.provenance, &right)
                {
                    return result;
                }
            }
        }
        (_, ExprContents::Lambda(lambda)) => {
            if !matches!(&left.contents, ExprContents::Lambda(_)) {
                // Test if the we can eta-expand the left expression into the form of the right lambda.
                if let Some(result) =
                    try_eta_expansion(env, meta_gen, lambda, &right.provenance, &left)
                {
                    return result;
                }
            }
        }
        _ => {}
    }

    // All strategies to prove definitional equality failed.
    Ok(false)
}

/// Tries some fast simplifications to test for definitional equality.
/// If this function returns a value, this is the answer to whether `left` and `right` are definitionally
/// equal. If this function doesn't return anything, we could not tell whether they were equal.
///
/// In particular, this function will return a value when both parameters are lambda, pi, or sort expressions.
fn quick_definitionally_equal<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Expr,
    right: &Expr,
) -> Option<Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>>> {
    match (&left.contents, &right.contents) {
        (fnodes::expr::ExprContents::Lambda(left), fnodes::expr::ExprContents::Lambda(right)) => {
            Some(lambda_definitionally_equal(env, meta_gen, left, right))
        }
        (fnodes::expr::ExprContents::Pi(left), fnodes::expr::ExprContents::Pi(right)) => {
            Some(pi_definitionally_equal(env, meta_gen, left, right))
        }
        (fnodes::expr::ExprContents::Sort(left), fnodes::expr::ExprContents::Sort(right)) => {
            Some(Ok(universe_definitionally_equal(&left.0, &right.0)))
        }
        _ => None,
    }
}

/// Lambdas are definitionally equal if their parameter types are equal and their bodies are equal.
fn lambda_definitionally_equal<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Lambda,
    right: &Lambda,
) -> Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if !definitionally_equal_core(env, meta_gen, &left.parameter_ty, &right.parameter_ty)? {
        return Ok(false);
    }
    // The parameter types are the same.
    // Now, substitute the parameter types in the body, and check if they are the same.
    let mut left_body = *left.result.clone();
    let mut right_body = *right.result.clone();
    instantiate(
        &mut left_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(left.generate_local(meta_gen)),
        ),
    );
    instantiate(
        &mut right_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(left.generate_local(meta_gen)),
        ),
    );
    definitionally_equal_core(env, meta_gen, &left_body, &right_body)
}

/// Pi expressions are definitionally equal if their parameter types are equal and their result types are equal.
fn pi_definitionally_equal<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Pi,
    right: &Pi,
) -> Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if !definitionally_equal_core(env, meta_gen, &left.parameter_ty, &right.parameter_ty)? {
        return Ok(false);
    }
    // The parameter types are the same.
    // Now, substitute the parameter types in the result types, and check if they are the same.
    let mut left_body = *left.result.clone();
    let mut right_body = *right.result.clone();
    instantiate(
        &mut left_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(left.generate_local(meta_gen)),
        ),
    );
    instantiate(
        &mut right_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(left.generate_local(meta_gen)),
        ),
    );
    definitionally_equal_core(env, meta_gen, &left_body, &right_body)
}

fn universe_definitionally_equal(left: &Universe, right: &Universe) -> bool {
    let mut left = left.clone();
    let mut right = right.clone();
    normalise_universe(&mut left);
    normalise_universe(&mut right);
    left.eq_ignoring_provenance(&right)
}

/// Returns true if `left` and `right` are proofs of the same proposition.
/// We say that any two proofs are equal by definition. This property is called proof irrelevance.
fn equal_propositions<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Expr,
    right: &Expr,
) -> Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>> {
    // If the type of `left_type` is `Prop` (that is, universe zero), then proof irrelevance applies.
    let left_type = infer_type_core(env, meta_gen, left, true)?;
    let mut left_type_type = infer_type_core(env, meta_gen, &left_type, true)?;
    to_weak_head_normal_form(env, &mut left_type_type);
    if left_type_type.eq_ignoring_provenance(&Expr::new_synthetic(ExprContents::Sort(Sort(
        Universe::new_synthetic(UniverseContents::UniverseZero),
    )))) {
        let right_type = infer_type_core(env, meta_gen, right, true)?;
        definitionally_equal_core(env, meta_gen, &left_type, &right_type)
    } else {
        Ok(false)
    }
}

/// Perform delta reduction at the heads of the input expressions
/// to try to check if two expressions are definitionally equal.
fn lazy_delta_reduction<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &mut Expr,
    right: &mut Expr,
) -> Option<Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>>> {
    loop {
        // Check if either the left function or right function can be delta reduced.
        let left_height = head_definition_height(env, left);
        let right_height = head_definition_height(env, right);
        if left_height.is_none() && right_height.is_none() {
            // If neither head is a definition, we can't do any delta reduction in this step.
            break None;
        }

        match left_height.cmp(&right_height) {
            Ordering::Less => {
                // The right height was higher, so unfold that expression first.
                unfold_definition(env, right);
                to_weak_head_normal_form(env, right);
            }
            Ordering::Greater => {
                // Conversely, in this case, the left height was heigher.
                unfold_definition(env, left);
                to_weak_head_normal_form(env, left);
            }
            Ordering::Equal => {
                // Both had the same height (and are reducible).
                // Since we can't prioritise one over the other, we will just unfold both definitions.
                // TODO: If the definitions to be unfolded match, we can optimise this path by
                // comparing arguments. This would short-circuit the delta reduction. Even if the
                // arguments are not definitionally equal, the function could still return the same
                // value in theory, so we can't always completely bypass the check.
                unfold_definition(env, left);
                unfold_definition(env, right);
                to_weak_head_normal_form(env, left);
                to_weak_head_normal_form(env, right);
            }
        }

        // Now that we've done some delta reduction, check if the resulting terms match.
        match quick_definitionally_equal(env, meta_gen, left, right) {
            Some(result) => break Some(result),
            None => continue,
        }
    }
}

/// Tries to check if the lambda and `expr` are definitionally equal by eta-expanding `expr`.
/// `expr` should not be a lambda.
fn try_eta_expansion<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    lambda: &Lambda,
    lambda_provenance: &Provenance,
    expr: &Expr,
) -> Option<Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>>> {
    let mut expr_type = match infer_type_core(env, meta_gen, expr, true) {
        Ok(value) => value,
        Err(err) => return Some(Err(err)),
    };

    to_weak_head_normal_form(env, &mut expr_type);
    if let ExprContents::Pi(_) = &expr_type.contents {
        let new_expr = Expr::new_with_provenance(
            &expr.provenance,
            ExprContents::Lambda(Lambda {
                parameter_name: lambda.parameter_name.clone(),
                binder_annotation: lambda.binder_annotation,
                parameter_ty: lambda.parameter_ty.clone(),
                result: Box::new(Expr::new_with_provenance(
                    &expr.provenance,
                    ExprContents::Apply(Apply {
                        function: Box::new(expr.clone()),
                        argument: Box::new(Expr::new_with_provenance(
                            &expr.provenance,
                            ExprContents::Bound(Bound {
                                index: DeBruijnIndex::zero(),
                            }),
                        )),
                    }),
                )),
            }),
        );
        Some(definitionally_equal_core(
            env,
            meta_gen,
            &Expr::new_with_provenance(lambda_provenance, ExprContents::Lambda(lambda.clone())),
            &new_expr,
        ))
    } else {
        None
    }
}
