use std::collections::HashMap;

use fcommon::{Path, Str};
use fnodes::{
    expr::*, AtomicSexprWrapper, ListSexpr, ListSexprWrapper, SexprParsable, SexprSerialiseExt,
};

use crate::ValueInferenceEngine;

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
