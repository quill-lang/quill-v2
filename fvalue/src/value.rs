use std::collections::HashMap;

use fcommon::Path;
use fnodes::expr::*;

/// A realisation of an object which may contain inference variables, and may be simplifiable.
/// Importantly, it contains no provenance about where it came from in the expression - all we care
/// about is its value.
/// It therefore contains no feather nodes, and is cloneable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialValue {
    IntroLocal(IntroLocal),

    IntroU64(IntroU64),
    IntroFalse,
    IntroTrue,
    IntroUnit,

    FormU64,
    FormBool,
    FormUnit,

    Inst(Path),
    Let(Let<PartialValue>),
    Lambda(Lambda<PartialValue>),
    Apply(Apply<PartialValue>),
    Var(Var),

    FormFunc(FormFunc<PartialValue>),
}

impl PartialValue {
    /// Replace all instances of inference variables with their values.
    pub fn replace_vars(&mut self, var_to_val: &HashMap<Var, PartialValue>) {
        match self {
            PartialValue::Let(Let { to_assign, body }) => {
                to_assign.replace_vars(var_to_val);
                body.replace_vars(var_to_val);
            }
            PartialValue::Lambda(Lambda { body, .. }) => {
                body.replace_vars(var_to_val);
            }
            PartialValue::Apply(Apply { function, .. }) => {
                function.replace_vars(var_to_val);
            }
            PartialValue::Var(var) => {
                if let Some(val) = var_to_val.get(var) {
                    *self = val.clone();
                }
            }
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                parameter.replace_vars(var_to_val);
                result.replace_vars(var_to_val);
            }
            _ => {}
        }
    }
}
