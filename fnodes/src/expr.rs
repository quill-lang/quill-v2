//! All types of expression and value are defined here.
//!
//! # Adding variants
//! When adding a new expression variant, make sure to derive [`ExprVariant`].
//! This will automatically create implementations of [`ExpressionVariant`],
//! [`ValueVariant`], and [`ListSexpr`], with suitable generic arguments.
//! Such types must always be structs.
//!
//! ### Generic argument names
//! We restrict the possible generic argument names and their functions in [`ExprVariant`].
//! Each generic argument may take one of two possible values, one for node-based expressions
//! ([`Expr`]), and one for value-based expressions ([`Value`]).
//!
//! - `E`: [`Expr`] or [`Value`]
//! - `N`: [`Name`] or [`Str`]
//! - `Q`: [`QualifiedName`] or [`fcommon::Path`]
//! - `C`: [`Component<Name, Expr>`] or [`ComponentContents<Str, Value>`]
//! - `U`: [`UniverseExpr`] or [`UniverseValue`].
//!
//! ### Serialisation keyword
//! The `#[list_sexpr_keyword = "..."]` attribute must be provided to provide the keyword
//! that will be used for the [`ListSexpr`] implementation.
//! If no keyword is desired (for example, for utility structs) then simply use the
//! attribute with no parameters: `#[list_sexpr_keyword]`.
//!
//! ### Field serialisation methods
//! Each field must be serialisable.
//! It must be tagged with one of the following three attributes:
//!
//! - `#[atomic]`: if this field implements [`AtomicSexpr`]
//! - `#[list]`: if this field implements [`ListSexpr`]
//! - `#[direct]`: if this field implements [`SexprParsable<Output = Self>`] and [`SexprSerialisable`].
//!
//! The choice of attribute will influence the serialisation method.
//!
//! ### Shadow names
//! When registering a new variant, care should be taken to consider the function of any uses
//! of `N`, which is a [`Name`] or a [`Str`].
//! If it is used in a shadow context (i.e. writing [`Shadow<N>`] to denote [`Shadow<Name>`]
//! or [`Shadow<Str>`]), then one of the following attributes should be used.
//!
//! - `#[binding_shadow_name]`: if this name is considered a binder (from any viewpoint)
//! - `#[binding_shadow_names]`: if this can be iterated over,
//!     and its elements are binders as in `#[binding_shadow_name]`
//! - `#[non_binding_shadow_name]`: if this name is not a binder, but simply the name
//!     of a previously bound value or node
//! - `#[non_binding_shadow_names]`: if this can be iterated over,
//!     and its elements are non-binders as in `#[non_binding_shadow_name]`
//!
//! ## Sub-expressions
//! Any use of `E` must be tagged with the attribute `#[sub_expr]` to show that it is a
//! sub-expression (or sub-value, if `E` is [`Value`]).
//! Like with shadow names, `#[sub_exprs]` can be used to denote an iterable field with
//! sub-expression values.
use std::collections::HashMap;

use crate::basic_nodes::*;
use crate::*;
use fcommon::{InternExt, Path, PathData, Span, Str};
use fnodes_macros::*;

pub trait ExpressionVariant {
    fn sub_expressions(&self) -> Vec<&Expr>;
    fn sub_expressions_mut(&mut self) -> Vec<&mut Expr>;
    /// A list of the local names bound in this expression.
    /// Not all binding names may a priori be visible to all sub-expressions.
    fn binding_shadow_names(&self) -> Vec<&Shadow<Name>>;
    /// A list of the local names used in this expression that were bound somewhere else.
    fn non_binding_shadow_names(&self) -> Vec<&Shadow<Name>>;

    /// Returns both binding and non-binding shadow names.
    fn shadow_names(&mut self) -> Vec<&Shadow<Name>> {
        self.binding_shadow_names()
            .into_iter()
            .chain(self.non_binding_shadow_names())
            .collect()
    }
}

/// Utility trait for converting expression types into value types.
pub trait ToValue {
    type Value;
    fn to_value(&self, db: &dyn InternExt) -> Self::Value;
}

impl<T> ToValue for Box<T>
where
    T: ToValue,
{
    type Value = Box<T::Value>;
    fn to_value(&self, db: &dyn InternExt) -> Self::Value {
        Box::new(self.as_ref().to_value(db))
    }
}

impl<T> ToValue for Vec<T>
where
    T: ToValue,
{
    type Value = Vec<T::Value>;
    fn to_value(&self, db: &dyn InternExt) -> Self::Value {
        self.iter().map(|x| x.to_value(db)).collect()
    }
}

impl ToValue for QualifiedName {
    type Value = Path;

    fn to_value(&self, db: &dyn InternExt) -> Self::Value {
        db.intern_path_data(PathData(self.0.iter().map(|x| x.contents).collect()))
    }
}

impl ToValue for Shadow<Name> {
    type Value = Shadow<Str>;

    fn to_value(&self, _: &dyn InternExt) -> Self::Value {
        Shadow {
            value: self.value.contents,
            id: self.id,
        }
    }
}

pub trait ValueVariant {
    fn sub_values(&self) -> Vec<&Value>;
    fn sub_values_mut(&mut self) -> Vec<&mut Value>;
    /// A list of the local names bound in this value.
    /// Not all binding names may a priori be visible to all sub-values.
    fn binding_shadow_names(&self) -> Vec<Shadow<Str>>;
    /// A list of the local names used in this expression that were bound somewhere else.
    fn non_binding_shadow_names(&self) -> Vec<Shadow<Str>>;
    /// See [`ValueVariant::binding_names`].
    fn binding_shadow_names_mut(&mut self) -> Vec<&mut Shadow<Str>>;
    /// See [`ValueVariant::non_binding_names`].
    fn non_binding_shadow_names_mut(&mut self) -> Vec<&mut Shadow<Str>>;

    /// Returns both binding and non-binding shadow names.
    fn shadow_names(&mut self) -> Vec<Shadow<Str>> {
        self.binding_shadow_names()
            .into_iter()
            .chain(self.non_binding_shadow_names())
            .collect()
    }
}

impl<'a> From<&'a Box<Expr>> for &'a Expr {
    fn from(boxed: &'a Box<Expr>) -> Self {
        boxed
    }
}

impl<'a> From<&'a mut Box<Expr>> for &'a mut Expr {
    fn from(boxed: &'a mut Box<Expr>) -> Self {
        &mut *boxed
    }
}

impl<'a> From<&'a Box<Value>> for &'a Value {
    fn from(boxed: &'a Box<Value>) -> Self {
        boxed
    }
}

impl<'a> From<&'a mut Box<Value>> for &'a mut Value {
    fn from(boxed: &'a mut Box<Value>) -> Self {
        &mut *boxed
    }
}

// TODO: Check for duplicates in each component-related thing.

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ComponentContents<N, E> {
    pub name: N,
    pub ty: E,
}

impl ValueVariant for ComponentContents<Str, Value> {
    fn sub_values(&self) -> Vec<&Value> {
        vec![&self.ty]
    }

    fn sub_values_mut(&mut self) -> Vec<&mut Value> {
        vec![&mut self.ty]
    }

    fn binding_shadow_names(&self) -> Vec<Shadow<Str>> {
        Vec::new()
    }

    fn non_binding_shadow_names(&self) -> Vec<Shadow<Str>> {
        Vec::new()
    }

    fn binding_shadow_names_mut(&mut self) -> Vec<&mut Shadow<Str>> {
        Vec::new()
    }

    fn non_binding_shadow_names_mut(&mut self) -> Vec<&mut Shadow<Str>> {
        Vec::new()
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
        let mut infos = ctx.process_component_info(db, self, ctx);
        infos.insert(
            0,
            ListSexprWrapper::serialise_into_node(ctx, db, &self.contents.ty),
        );
        infos.insert(0, self.contents.name.serialise(ctx, db));
        infos
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

    fn binding_shadow_names(&self) -> Vec<&Shadow<Name>> {
        Vec::new()
    }

    fn non_binding_shadow_names(&self) -> Vec<&Shadow<Name>> {
        Vec::new()
    }
}

// Begin describing the expressions in Feather.
// We start with universe expressions.

/// A concrete universe level.
/// Level `0` represents `Prop`, the type of (proof-irrelevant) propositions.
/// Level `1` represents `Type`, the type of all (small) types.
pub type UniverseLevel = u32;

#[derive(Debug, Copy, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "univn"]
pub struct UniverseNumber(#[atomic] pub UniverseLevel);

#[derive(Debug, Copy, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "univvar"]
pub struct UniverseVariable(#[atomic] pub Str);

#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "univadd"]
pub struct UniverseAdd<U> {
    #[list]
    #[sub_expr]
    pub term: Box<U>,
    #[atomic]
    pub addend: UniverseLevel,
}

/// Takes the larger universe of `left` and `right`.
#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "univmax"]
pub struct UniverseMax<U> {
    #[list]
    #[sub_expr]
    pub left: Box<U>,
    #[list]
    #[sub_expr]
    pub right: Box<U>,
}

/// Takes the larger universe of `left` and `right`, but if `right == 0`, then this just gives `0`.
#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "univimax"]
pub struct UniverseImpredicativeMax<U> {
    #[list]
    #[sub_expr]
    pub left: Box<U>,
    #[list]
    #[sub_expr]
    pub right: Box<U>,
}

gen_expr! { UniverseContents UniverseValue
    UniverseNumber,
    UniverseVariable,
    UniverseAdd<U>,
    UniverseMax<U>,
    UniverseImpredicativeMax<U>
}

pub type UniverseExpr = Node<UniverseContents>;

// Now we do all non-universe expressions.

/// A bound local variable inside an abstraction.
#[derive(Debug, Copy, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "bound"]
pub struct Bound(#[atomic] pub DeBruijnIndex);

/// Either a definition or an inductive data type.
/// Parametrised by a list of universe parameters.
#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "inst"]
pub struct Inst<Q, U> {
    #[list]
    pub name: Q,
    #[list]
    pub universes: Vec<U>,
}

#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "let"]
pub struct Let<N, E> {
    /// The name of the local variable to bind.
    #[list]
    #[binding_shadow_name]
    pub name_to_assign: Shadow<N>,
    /// The value to assign to the new bound variable.
    #[list]
    #[sub_expr]
    pub to_assign: Box<E>,
    /// The main body of the expression to be executed after assigning the value.
    #[list]
    #[sub_expr]
    pub body: Box<E>,
}

/// How should the argument to this function be given?
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinderAnnotation {
    /// The argument is to be given explicitly.
    Explicit,
    /// The argument is implicit, and is to be filled eagerly by the elaborator.
    ImplicitEager,
    /// The argument is implicit, and is to be filled by the elaborator only when another later parameter is given.
    ImplicitWeak,
    /// The argument is implicit, and is to be filled by the elaborator by typeclass resolution.
    ImplicitTypeclass,
}

impl AtomicSexpr for BinderAnnotation {
    fn parse_atom(_db: &dyn SexprParser, text: String) -> Result<Self, ParseErrorReason> {
        match &*text {
            "ex" => Ok(Self::Explicit),
            "imp" => Ok(Self::ImplicitEager),
            "weak" => Ok(Self::ImplicitWeak),
            "class" => Ok(Self::ImplicitTypeclass),
            _ => Err(ParseErrorReason::WrongKeyword {
                expected: "ex | imp | weak | class",
                found: text,
            }),
        }
    }

    fn serialise(&self, _ctx: &SexprSerialiseContext, _db: &dyn SexprParser) -> String {
        match self {
            BinderAnnotation::Explicit => "ex".to_string(),
            BinderAnnotation::ImplicitEager => "imp".to_string(),
            BinderAnnotation::ImplicitWeak => "weak".to_string(),
            BinderAnnotation::ImplicitTypeclass => "class".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "lam"]
pub struct Lambda<N, E> {
    /// The name of the parameter.
    #[list]
    #[binding_shadow_name]
    pub parameter_name: Shadow<N>,
    /// How the parameter should be filled when calling the function.
    #[atomic]
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    #[list]
    #[sub_expr]
    pub parameter_ty: Box<E>,
    /// The body of the lambda, also called the lambda term.
    #[list]
    #[sub_expr]
    pub result: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "pi"]
pub struct Pi<N, E> {
    /// The name of the parameter.
    #[list]
    #[binding_shadow_name]
    pub parameter_name: Shadow<N>,
    /// How the parameter should be filled when calling the function.
    #[atomic]
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    #[list]
    #[sub_expr]
    pub parameter_ty: Box<E>,
    /// The type of the result.
    #[list]
    #[sub_expr]
    pub result: Box<E>,
}

#[derive(Debug, Clone, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "ap"]
pub struct Apply<N> {
    /// The function to be invoked.
    #[list]
    #[non_binding_shadow_name]
    pub function: Shadow<N>,
    /// The argument to apply to the function.
    #[list]
    #[non_binding_shadow_name]
    pub argument: Shadow<N>,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ExprVariant)]
#[list_sexpr_keyword = "sort"]
pub struct Sort<U>(#[list] U);

/// An inference variable.
/// May have theoretically any type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ExprVariant)]
#[list_sexpr_keyword = "var"]
pub struct Metavariable(#[atomic] u32);

/// Used for inference, should not be used in functions manually.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, ExprVariant)]
#[list_sexpr_keyword = "localconst"]
pub struct LocalConstant {
    #[list]
    #[sub_expr]
    pub metavariable: Metavariable,
    // pub binder_annotation: BinderAnnotation,
}

/// Generates unique inference variable names.
pub struct MetavariableGenerator {
    next_var: Metavariable,
}

impl Default for MetavariableGenerator {
    fn default() -> Self {
        Self {
            next_var: Metavariable(0),
        }
    }
}

impl MetavariableGenerator {
    /// Creates a new variable generator.
    /// Its variables will all be greater than the provided "largest unusable" variable name.
    /// If one was not provided, no guarantees are made about name clashing.
    pub fn new(largest_unusable: Option<Metavariable>) -> Self {
        Self {
            next_var: Metavariable(largest_unusable.map_or(0, |x| x.0 + 1)),
        }
    }

    pub fn gen(&mut self) -> Metavariable {
        let result = self.next_var;
        self.next_var.0 += 1;
        result
    }
}

#[derive(Debug, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "ty"]
#[no_to_value_impl]
pub struct ExprTy(
    #[list]
    #[sub_expr]
    pub Expr,
);

#[derive(Debug, PartialEq, Eq, ExprVariant)]
#[list_sexpr_keyword = "pty"]
#[no_to_value_impl]
pub struct PartialExprTy(
    #[list]
    #[sub_expr]
    pub Value,
);

gen_expr! { ExprContents Value
    Bound,
    Inst<Q, U>,
    Let<N, E>,
    Lambda<N, E>,
    Pi<N, E>,
    Apply<N>,
    Sort<U>,
    Metavariable,
    LocalConstant,
}

// TODO: get rid of `nullary`

pub type Expr = Node<ExprContents>;

impl ListSexpr for UniverseExpr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        ctx: &mut SexprParseContext,
        db: &dyn SexprParser,
        span: Span,
        args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        UniverseContents::parse_list(ctx, db, span.clone(), args)
            .map(|univ_contents| Node::new(ctx.node_id_gen.gen(), span, univ_contents))
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        self.contents.serialise(ctx, db)
    }
}

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

/// A utility for printing values to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct ValuePrinter<'a> {
    db: &'a dyn SexprParser,
    /// Maps inference variables to the names we use to render them.
    inference_variable_names: HashMap<Metavariable, String>,
    /// When we see a new inference variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
}

impl<'a> ValuePrinter<'a> {
    pub fn new(db: &'a dyn SexprParser) -> Self {
        Self {
            db,
            inference_variable_names: Default::default(),
            type_variable_name: Default::default(),
        }
    }

    pub fn print_universe(&mut self, val: &UniverseValue) -> String {
        match val {
            UniverseValue::UniverseNumber(n) => n.0.to_string(),
            UniverseValue::UniverseVariable(var) => self.db.lookup_intern_string_data(var.0),
            UniverseValue::UniverseAdd(add) => {
                format!("{} + {}", self.print_universe(&add.term), add.addend)
            }
            UniverseValue::UniverseMax(max) => format!(
                "max ({}) ({})",
                self.print_universe(&max.left),
                self.print_universe(&max.right)
            ),
            UniverseValue::UniverseImpredicativeMax(imax) => {
                format!(
                    "imax ({}) ({})",
                    self.print_universe(&imax.left),
                    self.print_universe(&imax.right)
                )
            }
        }
    }

    pub fn print(&mut self, val: &Value) -> String {
        match val {
            Value::Bound(bound) => bound.0.to_string(),
            Value::Lambda(lambda) => {
                let contents = format!(
                    "{}: {}",
                    self.db
                        .lookup_intern_string_data(lambda.parameter_name.value),
                    self.print(&*lambda.parameter_ty)
                );
                let binder = match lambda.binder_annotation {
                    BinderAnnotation::Explicit => format!("({})", contents),
                    BinderAnnotation::ImplicitEager => format!("{{{}}}", contents),
                    BinderAnnotation::ImplicitWeak => format!("{{{{{}}}}}", contents),
                    BinderAnnotation::ImplicitTypeclass => format!("[{}]", contents),
                };
                format!("λ {}, {}", binder, self.print(&*lambda.result))
            }
            Value::Pi(pi) => {
                let contents = format!(
                    "{}: {}",
                    self.db.lookup_intern_string_data(pi.parameter_name.value),
                    self.print(&*pi.parameter_ty)
                );
                let binder = match pi.binder_annotation {
                    BinderAnnotation::Explicit => format!("({})", contents),
                    BinderAnnotation::ImplicitEager => format!("{{{}}}", contents),
                    BinderAnnotation::ImplicitWeak => format!("{{{{{}}}}}", contents),
                    BinderAnnotation::ImplicitTypeclass => format!("[{}]", contents),
                };
                format!("Π {}, {}", binder, self.print(&*pi.result))
            }
            Value::Sort(Sort(universe)) => match universe {
                UniverseValue::UniverseNumber(UniverseNumber(0)) => "Prop".to_string(),
                UniverseValue::UniverseNumber(UniverseNumber(1)) => "Type".to_string(),
                _ => format!("Sort {}", self.print_universe(universe)),
            },
            _ => unimplemented!(),
        }
    }

    fn get_name(&mut self, var: Metavariable) -> String {
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
