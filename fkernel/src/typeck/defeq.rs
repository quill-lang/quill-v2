use std::ops::ControlFlow;

use fcommon::Report;
use fnodes::{
    expr::*,
    universe::{Universe, UniverseContents},
};

use crate::{expr::instantiate, universe::normalise_universe};

use super::{
    env::Environment,
    infer::{infer_type, infer_type_core},
    whnf::to_weak_head_normal_form,
};

/// Returns true if the two expressions are definitionally equal.
pub fn definitionally_equal<'a>(
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

    // Test for equivalence by performing delta reduction.
    if let Some(result) = lazy_delta_reduction(env, meta_gen, &mut left, &mut right) {
        return result;
    }

    todo!()
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
            Some(Ok(universe_definitionally_equal(left, right)))
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
    if !definitionally_equal(env, meta_gen, &*left.parameter_ty, &*right.parameter_ty)? {
        return Ok(false);
    }
    // The parameter types are the same.
    // Now, substitute the parameter types in the body, and check if they are the same.
    let mut left_body = *left.result.clone();
    let mut right_body = *right.result.clone();
    let new_local = LocalConstant {
        name: left.parameter_name.clone(),
        metavariable: meta_gen.gen(*left.parameter_ty.clone()),
        binder_annotation: left.binder_annotation,
    };
    instantiate(
        &mut left_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    instantiate(
        &mut right_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    definitionally_equal(env, meta_gen, &left_body, &right_body)
}

/// Pi expressions are definitionally equal if their parameter types are equal and their result types are equal.
fn pi_definitionally_equal<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &Pi,
    right: &Pi,
) -> Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>> {
    if !definitionally_equal(env, meta_gen, &*left.parameter_ty, &*right.parameter_ty)? {
        return Ok(false);
    }
    // The parameter types are the same.
    // Now, substitute the parameter types in the result types, and check if they are the same.
    let mut left_body = *left.result.clone();
    let mut right_body = *right.result.clone();
    let new_local = LocalConstant {
        name: left.parameter_name.clone(),
        metavariable: meta_gen.gen(*left.parameter_ty.clone()),
        binder_annotation: left.binder_annotation,
    };
    instantiate(
        &mut left_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    instantiate(
        &mut right_body,
        &Expr::new_in_sexpr(
            env.source,
            left.parameter_name.provenance.span(),
            ExprContents::LocalConstant(new_local.clone()),
        ),
    );
    definitionally_equal(env, meta_gen, &left_body, &right_body)
}

fn universe_definitionally_equal(left: &Sort, right: &Sort) -> bool {
    let mut left = left.0.clone();
    let mut right = right.0.clone();
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
    let mut left_type = infer_type_core(env, meta_gen, left, true)?;
    let mut left_type_type = infer_type_core(env, meta_gen, &left_type, true)?;
    to_weak_head_normal_form(env, &mut left_type_type);
    if left_type_type.eq_ignoring_provenance(&Expr::new_synthetic(ExprContents::Sort(Sort(
        Universe::new_synthetic(UniverseContents::UniverseZero),
    )))) {
        let right_type = infer_type_core(env, meta_gen, left, true)?;
        definitionally_equal(env, meta_gen, &left_type, &right_type)
    } else {
        Ok(false)
    }
}

fn lazy_delta_reduction<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &mut Expr,
    right: &mut Expr,
) -> Option<Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>>> {
    loop {
        match delta_reduction_step(env, meta_gen, left, right) {
            ControlFlow::Continue(()) => continue,
            ControlFlow::Break(result) => break result,
        }
    }
}

fn delta_reduction_step<'a>(
    env: &'a Environment,
    meta_gen: &mut MetavariableGenerator,
    left: &mut Expr,
    right: &mut Expr,
) -> ControlFlow<Option<Result<bool, Box<dyn FnOnce(Report) -> Report + 'a>>>> {
    todo!()
}
