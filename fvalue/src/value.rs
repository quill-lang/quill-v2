use std::collections::HashMap;

use fcommon::{Path, Str};
use fnodes::{
    expr::*, AtomicSexprWrapper, ListSexpr, ListSexprWrapper, SexprParsable, SexprSerialiseExt,
};

use crate::ValueInferenceEngine;

/// A realisation of an object which may contain inference variables, and may be simplifiable.
/// Importantly, it contains no provenance about where it came from in the expression - all we care
/// about is its value.
/// It therefore contains no feather nodes, and is cloneable.
///
/// # Adding variants
/// When adding a new variant to [`PartialValue`], make sure to update:
/// - [`PartialValue::sub_expressions`]
/// - [`PartialValue::sub_expressions_mut`]
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

    IntroProduct(IntroProduct<Str, PartialValue>),
    /// Here, the components may not have names - this is simply for the purpose of inference.
    /// Once type inference is done, we will know all fields' names.
    FormProduct(FormProduct<ComponentContents<Str, PartialValue>>),
    MatchProduct(MatchProduct<Str, PartialValue>),

    Inst(Path),
    Let(Let<PartialValue>),
    Lambda(Lambda<PartialValue>),
    Apply(Apply<PartialValue>),
    Var(Var),

    FormFunc(FormFunc<PartialValue>),

    FormUniverse,
}

impl PartialValue {
    pub fn sub_expressions(&self) -> Vec<&PartialValue> {
        match self {
            PartialValue::IntroProduct(IntroProduct { fields }) => {
                fields.iter().map(|comp| &comp.expr).collect()
            }
            PartialValue::FormProduct(FormProduct { fields }) => {
                fields.iter().map(|comp| &comp.ty).collect()
            }
            PartialValue::MatchProduct(MatchProduct { product, body, .. }) => {
                vec![product, body]
            }
            PartialValue::Let(Let { to_assign, body }) => vec![&*to_assign, &*body],
            PartialValue::Lambda(Lambda { body, .. }) => vec![&*body],
            PartialValue::Apply(Apply { function, .. }) => vec![&*function],
            PartialValue::FormFunc(FormFunc { parameter, result }) => vec![&*parameter, &*result],
            _ => Vec::new(),
        }
    }

    pub fn sub_expressions_mut(&mut self) -> Vec<&mut PartialValue> {
        match self {
            PartialValue::IntroProduct(IntroProduct { fields }) => {
                fields.iter_mut().map(|comp| &mut comp.expr).collect()
            }
            PartialValue::FormProduct(FormProduct { fields }) => {
                fields.iter_mut().map(|comp| &mut comp.ty).collect()
            }
            PartialValue::MatchProduct(MatchProduct { product, body, .. }) => {
                vec![product, body]
            }
            PartialValue::Let(Let { to_assign, body }) => vec![&mut *to_assign, &mut *body],
            PartialValue::Lambda(Lambda { body, .. }) => vec![&mut *body],
            PartialValue::Apply(Apply { function, .. }) => vec![&mut *function],
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                vec![&mut *parameter, &mut *result]
            }
            _ => Vec::new(),
        }
    }

    /// Replace all instances of inference variables with their values.
    pub fn replace_vars(&mut self, var_to_val: &HashMap<Var, PartialValue>) {
        match self {
            PartialValue::Var(var) => {
                if let Some(val) = var_to_val.get(var) {
                    *self = val.clone();
                }
            }
            _ => {
                for expr in self.sub_expressions_mut() {
                    expr.replace_vars(var_to_val)
                }
            }
        }
    }
}

/// A utility for printing partial values to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct PartialValuePrinter<'a> {
    db: &'a dyn ValueInferenceEngine,
    /// Maps inference variables to the names we use to render them.
    inference_variable_names: HashMap<Var, String>,
    /// When we see a new inference variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
}

impl<'a> PartialValuePrinter<'a> {
    pub fn new(db: &'a dyn ValueInferenceEngine) -> Self {
        Self {
            db,
            inference_variable_names: Default::default(),
            type_variable_name: Default::default(),
        }
    }

    pub fn print(&mut self, val: &PartialValue) -> String {
        match val {
            PartialValue::IntroLocal(_) => todo!(),
            PartialValue::IntroU64(_) => todo!(),
            PartialValue::IntroFalse => todo!(),
            PartialValue::IntroTrue => todo!(),
            PartialValue::IntroUnit => todo!(),
            PartialValue::FormU64 => "U64".to_string(),
            PartialValue::FormBool => todo!(),
            PartialValue::FormUnit => "Unit".to_string(),
            PartialValue::IntroProduct(_) => todo!(),
            PartialValue::FormProduct(FormProduct { fields }) => {
                let fields = fields
                    .iter()
                    .map(|comp| {
                        format!(
                            "{}: {}",
                            self.db.lookup_intern_string_data(comp.name),
                            self.print(&comp.ty)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{}}}", fields)
            }
            PartialValue::MatchProduct(_) => todo!(),
            PartialValue::Inst(_) => todo!(),
            PartialValue::Let(_) => todo!(),
            PartialValue::Lambda(_) => todo!(),
            PartialValue::Apply(_) => todo!(),
            PartialValue::Var(var) => self.get_name(*var),
            PartialValue::FormFunc(FormFunc { parameter, result }) => {
                // TODO: Check precedence with (->) symbol.
                // Perhaps unify this with some generic node pretty printer?
                format!("{} -> {}", self.print(parameter), self.print(result))
            }
            PartialValue::FormUniverse => "Universe".to_string(),
        }
    }

    fn get_name(&mut self, var: Var) -> String {
        if let Some(result) = self.inference_variable_names.get(&var) {
            result.clone()
        } else {
            let name = self.new_name();
            self.inference_variable_names.insert(var, name.clone());
            name
        }
    }

    fn new_name(&mut self) -> String {
        let id = self.type_variable_name;
        self.type_variable_name += 1;

        // Assign a new lowercase Greek letter to this type.
        // There are 24 letters to choose from.
        // If we overflow this, just add a suffix to the name.
        let name = std::char::from_u32('α' as u32 + (id % 24)).unwrap();
        let suffix = id / 24;
        if suffix > 0 {
            format!("{}{}", name, suffix)
        } else {
            format!("{}", name)
        }
    }
}

impl ListSexpr for PartialValue {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut fnodes::SexprParseContext,
        db: &dyn fnodes::SexprParser,
        span: fcommon::Span,
        args: Vec<fnodes::SexprNode>,
    ) -> Result<Self, fnodes::ParseError> {
        todo!()
    }

    fn serialise(
        &self,
        ctx: &fnodes::SexprSerialiseContext,
        db: &dyn fnodes::SexprParser,
    ) -> Vec<fnodes::SexprNode> {
        match self {
            PartialValue::FormUnit => {
                let mut result = FormUnit.serialise(ctx, db);
                result.insert(
                    0,
                    AtomicSexprWrapper::serialise_into_node(
                        ctx,
                        db,
                        &FormUnit::KEYWORD.unwrap().to_string(),
                    ),
                );
                result
            }
            PartialValue::FormU64 => {
                let mut result = FormU64.serialise(ctx, db);
                result.insert(
                    0,
                    AtomicSexprWrapper::serialise_into_node(
                        ctx,
                        db,
                        &FormU64::KEYWORD.unwrap().to_string(),
                    ),
                );
                result
            }
            PartialValue::FormProduct(val) => {
                let mut result = val.serialise(ctx, db);
                result.insert(
                    0,
                    AtomicSexprWrapper::serialise_into_node(
                        ctx,
                        db,
                        &FormProduct::<ComponentContents<Str, PartialValue>>::KEYWORD
                            .unwrap()
                            .to_string(),
                    ),
                );
                result
            }
            PartialValue::FormFunc(val) => {
                let mut result = val.serialise(ctx, db);
                result.insert(
                    0,
                    AtomicSexprWrapper::serialise_into_node(
                        ctx,
                        db,
                        &FormFunc::<PartialValue>::KEYWORD.unwrap().to_string(),
                    ),
                );
                result
            }
            _ => todo!("self was {:#?}", self),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct PartialExprTy(pub PartialValue);

impl ListSexpr for PartialExprTy {
    const KEYWORD: Option<&'static str> = Some("pty");

    fn parse_list(
        ctx: &mut fnodes::SexprParseContext,
        db: &dyn fnodes::SexprParser,
        span: fcommon::Span,
        args: Vec<fnodes::SexprNode>,
    ) -> Result<Self, fnodes::ParseError> {
        let [value] = fnodes::force_arity(span, args)?;
        ListSexprWrapper::parse(ctx, db, value).map(Self)
    }

    fn serialise(
        &self,
        ctx: &fnodes::SexprSerialiseContext,
        db: &dyn fnodes::SexprParser,
    ) -> Vec<fnodes::SexprNode> {
        vec![ListSexprWrapper::serialise_into_node(ctx, db, &self.0)]
    }
}
