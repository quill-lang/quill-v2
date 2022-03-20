use std::collections::HashMap;

use crate::basic_nodes::*;
use crate::*;
use fcommon::{Span, Str};
use fnodes_macros::*;

pub trait ExpressionVariant {
    fn sub_expressions(&self) -> Vec<&Expr>;
    fn sub_expressions_mut(&mut self) -> Vec<&mut Expr>;
}

pub trait PartialValueVariant {
    fn sub_values(&self) -> Vec<&PartialValue>;
    fn sub_values_mut(&mut self) -> Vec<&mut PartialValue>;
}

impl<'a> From<&'a Box<Expr>> for &'a Expr {
    fn from(boxed: &'a Box<Expr>) -> Self {
        &*boxed
    }
}

impl<'a> From<&'a mut Box<Expr>> for &'a mut Expr {
    fn from(boxed: &'a mut Box<Expr>) -> Self {
        &mut *boxed
    }
}

impl<'a> From<&'a Box<PartialValue>> for &'a PartialValue {
    fn from(boxed: &'a Box<PartialValue>) -> Self {
        &*boxed
    }
}

impl<'a> From<&'a mut Box<PartialValue>> for &'a mut PartialValue {
    fn from(boxed: &'a mut Box<PartialValue>) -> Self {
        &mut *boxed
    }
}

// TODO: Check for duplicates in each component-related thing.

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ComponentContents<N, E> {
    pub name: N,
    pub ty: E,
}

impl PartialValueVariant for ComponentContents<Str, PartialValue> {
    fn sub_values(&self) -> Vec<&PartialValue> {
        vec![&self.ty]
    }

    fn sub_values_mut(&mut self) -> Vec<&mut PartialValue> {
        vec![&mut self.ty]
    }
}

pub type Component<N, E> = Node<ComponentContents<N, E>>;

impl ListSexpr for Component<Name, Expr> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.len() < 2 {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::WrongArity {
                    expected_arity: 2,
                    found_arity: args.len(),
                },
            });
        }
        let name = Name::parse(ctx, db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(ctx, db, args.remove(0))?;
        let component = Node::new(ctx.node_id_gen.gen(), span, ComponentContents { name, ty });
        for info in args {
            ctx.process_component_info(db, &component, info)?;
        }
        Ok(component)
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: component info
        vec![
            self.contents.name.serialise(ctx, db),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.ty),
        ]
    }
}

impl<E> ListSexpr for ComponentContents<Str, E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.len() < 2 {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::WrongArity {
                    expected_arity: 2,
                    found_arity: args.len(),
                },
            });
        }
        let name = AtomicSexprWrapper::parse(ctx, db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(ctx, db, args.remove(0))?;
        Ok(ComponentContents { name, ty })
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(ctx, db, &self.name),
            ListSexprWrapper::serialise_into_node(ctx, db, &self.ty),
        ]
    }
}

impl ExpressionVariant for Component<Name, Expr> {
    fn sub_expressions(&self) -> Vec<&Expr> {
        vec![&self.contents.ty]
    }

    fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
        vec![&mut self.contents.ty]
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "local"]
pub struct IntroLocal(#[atomic] pub DeBruijnIndex);

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "ifalse"]
pub struct IntroFalse;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "itrue"]
pub struct IntroTrue;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "iunit"]
pub struct IntroUnit;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "fu64"]
pub struct FormU64;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "fbool"]
pub struct FormBool;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "funit"]
pub struct FormUnit;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "iu64"]
pub struct IntroU64(#[atomic] pub u64);

#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword]
pub struct IntroComponent<N, E> {
    #[direct]
    pub name: N,
    #[list]
    #[sub_expr]
    pub expr: E,
}

#[derive(Debug, PartialEq, Eq, Clone, ListSexpr)]
#[list_sexpr_keyword = "iprod"]
pub struct IntroProduct<N, E> {
    #[list_flatten]
    #[sub_exprs_flatten]
    pub fields: Vec<IntroComponent<N, E>>,
}

#[derive(Debug, PartialEq, Eq, Clone, ListSexpr)]
#[list_sexpr_keyword = "fprod"]
pub struct FormProduct<C> {
    #[list_flatten]
    #[sub_exprs_flatten]
    pub fields: Vec<C>,
}

#[derive(Debug, PartialEq, Eq, Clone, ListSexpr)]
#[list_sexpr_keyword = "mprod"]
pub struct MatchProduct<N, E> {
    #[list]
    pub fields: Vec<N>,
    #[list]
    #[sub_expr]
    pub product: Box<E>,
    #[list]
    #[sub_expr]
    pub body: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "inst"]
pub struct Inst<Q>(#[list] pub Q);

#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "let"]
pub struct Let<E> {
    /// The value to assign to the new bound variable.
    #[list]
    #[sub_expr]
    pub to_assign: Box<E>,
    /// The main body of the expression to be executed after assigning the value.
    #[list]
    #[sub_expr]
    pub body: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "lambda"]
pub struct Lambda<E> {
    /// The amount of new variables to be bound in the body of the lambda.
    #[atomic]
    pub binding_count: u32,
    /// The body of the lambda, also called the lambda term.
    #[list]
    #[sub_expr]
    pub body: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "ap"]
pub struct Apply<E> {
    /// The function to be invoked.
    #[list]
    #[sub_expr]
    pub function: Box<E>,
    /// The argument to apply to the function.
    #[atomic]
    pub argument: DeBruijnIndex,
}

/// An inference variable.
/// May have theoretically any type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ListSexpr)]
#[list_sexpr_keyword = "var"]
pub struct Var(#[atomic] u32);

/// Generates unique inference variable names.
pub struct VarGenerator {
    next_var: Var,
}

impl Default for VarGenerator {
    fn default() -> Self {
        Self { next_var: Var(0) }
    }
}

impl VarGenerator {
    pub fn gen(&mut self) -> Var {
        let result = self.next_var;
        self.next_var.0 += 1;
        result
    }
}

// TODO: Document this in the spec.
#[derive(Debug, Clone, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "ffunc"]
pub struct FormFunc<E> {
    /// The type of the parameter.
    #[list]
    #[sub_expr]
    pub parameter: Box<E>,
    /// The type of the result.
    #[list]
    #[sub_expr]
    pub result: Box<E>,
}

#[derive(Debug, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "funiverse"]
pub struct FormUniverse;

#[derive(Debug, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "ty"]
pub struct ExprTy(
    #[list]
    #[sub_expr]
    pub Expr,
);

#[derive(Debug, PartialEq, Eq, ListSexpr)]
#[list_sexpr_keyword = "pty"]
pub struct PartialExprTy(
    #[list]
    #[sub_expr]
    pub PartialValue,
);

gen_expr! {
    IntroLocal,

    IntroU64,
    nullary IntroFalse,
    nullary IntroTrue,
    nullary IntroUnit,

    nullary FormU64,
    nullary FormBool,
    nullary FormUnit,

    IntroProduct<N, E>,
    FormProduct<C>,
    MatchProduct<N, E>,

    Inst<Q>,
    Let<E>,
    Lambda<E>,
    Apply<E>,
    Var,

    FormFunc<E>,

    nullary FormUniverse,
}

pub type Expr = Node<ExprContents>;

impl ListSexpr for Expr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        // If the first arg is `expr`, this is of the form `expr ExprContents ExprInfo*`.
        let expr_check = args.first().map(|node| {
            if let SexprNodeContents::Atom(string) = &node.contents {
                string == "expr"
            } else {
                false
            }
        });
        if let Some(true) = expr_check {
            // This is of the form `expr ExprContents ExprInfo*`.
            if args.len() < 2 {
                return Err(ParseError {
                    span,
                    reason: ParseErrorReason::WrongArity {
                        expected_arity: 2,
                        found_arity: 1,
                    },
                });
            }
            let _expr_keyword = args.remove(0);
            let expr_contents = ListSexprWrapper::<ExprContents>::parse(ctx, db, args.remove(0))?;
            let expr = Node::new(ctx.node_id_gen.gen(), span, expr_contents);
            for info in args {
                ctx.process_expr_info(db, &expr, info)?;
            }
            Ok(expr)
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(ctx, db, span.clone(), args)
                .map(|expr_contents| Node::new(ctx.node_id_gen.gen(), span, expr_contents))
        }
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let mut infos = ctx.process_expr_info(db, self, ctx);
        if infos.is_empty() {
            self.contents.serialise(ctx, db)
        } else {
            infos.insert(
                0,
                ListSexprWrapper::serialise_into_node(ctx, db, &self.contents),
            );
            infos.insert(
                0,
                AtomicSexprWrapper::serialise_into_node(ctx, db, &"expr".to_string()),
            );
            infos
        }
    }
}

/// A utility for printing partial values to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct PartialValuePrinter<'a> {
    db: &'a dyn SexprParser,
    /// Maps inference variables to the names we use to render them.
    inference_variable_names: HashMap<Var, String>,
    /// When we see a new inference variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
}

impl<'a> PartialValuePrinter<'a> {
    pub fn new(db: &'a dyn SexprParser) -> Self {
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
