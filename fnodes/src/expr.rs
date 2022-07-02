//! All types of expression and value are defined here.
//!
//! TODO: This is out of date.
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

use crate::universe::{Metauniverse, UniverseContents};
use crate::*;
use crate::{basic_nodes::*, universe::Universe};
use fcommon::{Source, Span};
use fnodes_macros::*;

pub trait ExpressionVariant {
    fn sub_expressions(&self) -> Vec<&Expr>;
    fn sub_expressions_mut(&mut self) -> Vec<&mut Expr>;
}

// TODO: Check for duplicates in each component-related thing.

/*#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ComponentContents<N, E> {
    pub name: N,
    pub ty: E,
}

pub type Component<N, E> = Node<ComponentContents<N, E>>;

impl ListSexpr for Component<Name, Expr> {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
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
        let name = Name::parse(db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(db, args.remove(0))?;
        let component =
            Node::new_in_sexpr(ctx.node_id_gen.gen(), span, ComponentContents { name, ty });
        for info in args {
            ctx.process_component_info(db, &component, info)?;
        }
        Ok(component)
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        let mut infos = ctx.process_component_info(db, self, ctx);
        infos.insert(
            0,
            ListSexprWrapper::serialise_into_node(db, &self.contents.ty),
        );
        infos.insert(0, self.contents.name.serialise(db));
        infos
    }
}

impl<E> ListSexpr for ComponentContents<Str, E>
where
    E: ListSexpr,
{
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
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
        let name = AtomicSexprWrapper::parse(db, args.remove(0))?;
        let ty = ListSexprWrapper::parse(db, args.remove(0))?;
        Ok(ComponentContents { name, ty })
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        vec![
            AtomicSexprWrapper::serialise_into_node(db, &self.name),
            ListSexprWrapper::serialise_into_node(db, &self.ty),
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
}*/

// Begin describing the expressions in Feather.

/// A bound local variable inside an abstraction.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "bound"]
pub struct Bound {
    #[atomic]
    pub index: DeBruijnIndex,
}

/// Either a definition or an inductive data type.
/// Parametrised by a list of universe parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "inst"]
pub struct Inst {
    #[list]
    pub name: QualifiedName,
    #[list]
    pub universes: Vec<Universe>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "let"]
pub struct Let {
    /// The name of the local variable to bind.
    #[direct]
    pub name_to_assign: Name,
    /// The value to assign to the new bound variable.
    #[list]
    #[sub_expr]
    pub to_assign: Box<Expr>,
    /// The type of the value to assign to the bound variable.
    #[list]
    #[sub_expr]
    pub to_assign_ty: Box<Expr>,
    /// The main body of the expression to be executed after assigning the value.
    #[list]
    #[sub_expr]
    pub body: Box<Expr>,
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
    fn parse_atom(
        _db: &dyn SexprParser,
        _source: Source,
        text: String,
    ) -> Result<Self, ParseErrorReason> {
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

    fn serialise(&self, _db: &dyn SexprParser) -> String {
        match self {
            BinderAnnotation::Explicit => "ex".to_string(),
            BinderAnnotation::ImplicitEager => "imp".to_string(),
            BinderAnnotation::ImplicitWeak => "weak".to_string(),
            BinderAnnotation::ImplicitTypeclass => "class".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "lam"]
pub struct Lambda {
    /// The name of the parameter.
    #[direct]
    pub parameter_name: Name,
    /// How the parameter should be filled when calling the function.
    #[atomic]
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    #[list]
    #[sub_expr]
    pub parameter_ty: Box<Expr>,
    /// The body of the lambda, also called the lambda term.
    #[list]
    #[sub_expr]
    pub result: Box<Expr>,
}

impl Lambda {
    /// Generates a local constant that represents the argument to this lambda abstraction.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator) -> LocalConstant {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(*self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "pi"]
pub struct Pi {
    /// The name of the parameter.
    #[direct]
    pub parameter_name: Name,
    /// How the parameter should be filled when calling the function.
    #[atomic]
    pub binder_annotation: BinderAnnotation,
    /// The type of the parameter.
    #[list]
    #[sub_expr]
    pub parameter_ty: Box<Expr>,
    /// The type of the result.
    #[list]
    #[sub_expr]
    pub result: Box<Expr>,
}

impl Pi {
    /// Generates a local constant that represents the argument to this dependent function type.
    pub fn generate_local(&self, meta_gen: &mut MetavariableGenerator) -> LocalConstant {
        LocalConstant {
            name: self.parameter_name.clone(),
            metavariable: meta_gen.gen(*self.parameter_ty.clone()),
            binder_annotation: self.binder_annotation,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "ap"]
pub struct Apply {
    /// The function to be invoked.
    #[list]
    pub function: Box<Expr>,
    /// The argument to apply to the function.
    #[list]
    pub argument: Box<Expr>,
}

/// Represents the universe of types corresponding to the given universe.
/// For example, if the universe is `0`, this is `Prop`, the type of propositions.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "sort"]
pub struct Sort(#[list] pub Universe);

/// An inference variable.
/// May have theoretically any type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "meta"]
pub struct Metavariable {
    #[atomic]
    pub index: u32,
    /// We store the types of metavariables explicitly, since they can't be inferred.
    #[list]
    #[sub_expr]
    pub ty: Box<Expr>,
}

/// De Bruijn indices (bound variables) are replaced with local constants while we're inside the function body.
/// Should not be used in functions manually.
#[derive(Debug, Clone, PartialEq, Eq, Hash, ExprVariant)]
#[list_sexpr_keyword = "localconst"]
pub struct LocalConstant {
    /// The position of the name is where it was defined, not where it was used.
    #[direct]
    pub name: Name,
    #[list]
    pub metavariable: Metavariable,
    /// How was this local variable introduced?
    #[atomic]
    pub binder_annotation: BinderAnnotation,
}

/// Generates unique inference variable names.
pub struct MetavariableGenerator {
    next_var: u32,
}

impl Default for MetavariableGenerator {
    fn default() -> Self {
        Self { next_var: 0 }
    }
}

impl MetavariableGenerator {
    /// Creates a new variable generator.
    /// Its variables will all be greater than the provided "largest unusable" variable name.
    /// If one was not provided, no guarantees are made about name clashing.
    pub fn new(largest_unusable: Option<Metavariable>) -> Self {
        Self {
            next_var: largest_unusable.map_or(0, |x| x.index + 1),
        }
    }

    pub fn gen(&mut self, ty: Expr) -> Metavariable {
        let result = self.next_var;
        self.next_var += 1;
        Metavariable {
            index: result,
            ty: Box::new(ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprContents {
    Bound(Bound),
    Inst(Inst),
    Let(Let),
    Lambda(Lambda),
    Pi(Pi),
    Apply(Apply),
    Sort(Sort),
    Metavariable(Metavariable),
    LocalConstant(LocalConstant),
}

impl ExprContents {
    fn variant_keyword(&self) -> &'static str {
        match self {
            Self::Bound(_) => Bound::KEYWORD.unwrap(),
            Self::Inst(_) => Inst::KEYWORD.unwrap(),
            Self::Let(_) => Let::KEYWORD.unwrap(),
            Self::Lambda(_) => Lambda::KEYWORD.unwrap(),
            Self::Pi(_) => Pi::KEYWORD.unwrap(),
            Self::Apply(_) => Apply::KEYWORD.unwrap(),
            Self::Sort(_) => Sort::KEYWORD.unwrap(),
            Self::Metavariable(_) => Metavariable::KEYWORD.unwrap(),
            Self::LocalConstant(_) => LocalConstant::KEYWORD.unwrap(),
        }
    }
}

impl ListSexpr for ExprContents {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
        span: Span,
        mut args: Vec<SexprNode>,
    ) -> Result<Self, ParseError> {
        if args.is_empty() {
            return Err(ParseError {
                span,
                reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                    expected: "<any expression>",
                },
            });
        }

        let first = args.remove(0);
        let keyword = if let SexprNodeContents::Atom(value) = &first.contents {
            value.as_str()
        } else {
            return Err(ParseError {
                span: first.span.clone(),
                reason: ParseErrorReason::ExpectedKeywordFoundList {
                    expected: "<any expression>",
                },
            });
        };

        // Reduce the span to only contain the arguments, not the keyword.
        let span = (first.span.end + 1)..span.end - 1;

        Ok(match Some(keyword) {
            Bound::KEYWORD => Self::Bound(Bound::parse_list(db, source, span, args)?),
            Inst::KEYWORD => Self::Inst(Inst::parse_list(db, source, span, args)?),
            Let::KEYWORD => Self::Let(Let::parse_list(db, source, span, args)?),
            Lambda::KEYWORD => Self::Lambda(Lambda::parse_list(db, source, span, args)?),
            Pi::KEYWORD => Self::Pi(Pi::parse_list(db, source, span, args)?),
            Apply::KEYWORD => Self::Apply(Apply::parse_list(db, source, span, args)?),
            Sort::KEYWORD => Self::Sort(Sort::parse_list(db, source, span, args)?),
            Metavariable::KEYWORD => {
                Self::Metavariable(Metavariable::parse_list(db, source, span, args)?)
            }
            LocalConstant::KEYWORD => {
                Self::LocalConstant(LocalConstant::parse_list(db, source, span, args)?)
            }
            _ => {
                return Err(ParseError {
                    span: first.span.clone(),
                    reason: ParseErrorReason::WrongKeyword {
                        expected: "<any expression>",
                        found: keyword.to_string(),
                    },
                })
            }
        })
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        // TODO: expr infos
        let mut result = match self {
            Self::Bound(val) => val.serialise(db),
            Self::Inst(val) => val.serialise(db),
            Self::Let(val) => val.serialise(db),
            Self::Lambda(val) => val.serialise(db),
            Self::Pi(val) => val.serialise(db),
            Self::Apply(val) => val.serialise(db),
            Self::Sort(val) => val.serialise(db),
            Self::Metavariable(val) => val.serialise(db),
            Self::LocalConstant(val) => val.serialise(db),
        };
        result.insert(
            0,
            SexprNode {
                contents: SexprNodeContents::Atom(self.variant_keyword().to_owned()),
                span: 0..0,
            },
        );
        result
    }
}

impl ExprContents {
    pub fn sub_expressions(&self) -> Vec<&Expr> {
        match self {
            Self::Bound(val) => val.sub_expressions(),
            Self::Inst(val) => val.sub_expressions(),
            Self::Let(val) => val.sub_expressions(),
            Self::Lambda(val) => val.sub_expressions(),
            Self::Pi(val) => val.sub_expressions(),
            Self::Apply(val) => val.sub_expressions(),
            Self::Sort(val) => val.sub_expressions(),
            Self::Metavariable(val) => val.sub_expressions(),
            Self::LocalConstant(val) => val.sub_expressions(),
        }
    }

    pub fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
        match self {
            Self::Bound(val) => val.sub_expressions_mut(),
            Self::Inst(val) => val.sub_expressions_mut(),
            Self::Let(val) => val.sub_expressions_mut(),
            Self::Lambda(val) => val.sub_expressions_mut(),
            Self::Pi(val) => val.sub_expressions_mut(),
            Self::Apply(val) => val.sub_expressions_mut(),
            Self::Sort(val) => val.sub_expressions_mut(),
            Self::Metavariable(val) => val.sub_expressions_mut(),
            Self::LocalConstant(val) => val.sub_expressions_mut(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    /// The origin of the expression.
    pub provenance: Provenance,
    /// The actual contents of this expression.
    pub contents: ExprContents,
    /// If the expression has a type annotation, the type is given here.
    pub ty: Option<Box<Expr>>,
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:?}@{:#?}", self.provenance, self.contents)
        } else {
            write!(f, "{:?}@{:?}", self.provenance, self.contents)
        }
    }
}

impl Expr {
    pub fn new_in_sexpr(source: Source, span: Span, contents: ExprContents) -> Self {
        Self {
            provenance: Provenance::Sexpr { source, span },
            contents,
            ty: None,
        }
    }

    pub fn new_synthetic(contents: ExprContents) -> Self {
        Self {
            provenance: Provenance::Synthetic,
            contents,
            ty: None,
        }
    }

    pub fn new_with_provenance(provenance: &Provenance, contents: ExprContents) -> Self {
        Self {
            provenance: provenance.clone(),
            contents,
            ty: None,
        }
    }

    /// Returns a dummy expression.
    /// Should not be used for anything.
    pub fn dummy() -> Self {
        Self::new_synthetic(ExprContents::Sort(Sort(Universe::dummy())))
    }

    /// Compares two expressions for equality, ignoring the provenance data.
    pub fn eq_ignoring_provenance(&self, other: &Expr) -> bool {
        let result = match (&self.contents, &other.contents) {
            (ExprContents::Bound(left), ExprContents::Bound(right)) => left.index == right.index,
            (ExprContents::Inst(left), ExprContents::Inst(right)) => todo!(),
            (ExprContents::Let(left), ExprContents::Let(right)) => todo!(),
            (ExprContents::Lambda(left), ExprContents::Lambda(right)) => {
                left.parameter_name
                    .eq_ignoring_provenance(&right.parameter_name)
                    && left.binder_annotation == right.binder_annotation
                    && left
                        .parameter_ty
                        .eq_ignoring_provenance(&right.parameter_ty)
                    && left.result.eq_ignoring_provenance(&right.result)
            }
            (ExprContents::Pi(left), ExprContents::Pi(right)) => todo!(),
            (ExprContents::Apply(left), ExprContents::Apply(right)) => {
                left.argument.eq_ignoring_provenance(&right.argument)
                    && left.function.eq_ignoring_provenance(&right.function)
            }
            (ExprContents::Sort(left), ExprContents::Sort(right)) => {
                left.0.eq_ignoring_provenance(&right.0)
            }
            (ExprContents::Metavariable(left), ExprContents::Metavariable(right)) => todo!(),
            (ExprContents::LocalConstant(left), ExprContents::LocalConstant(right)) => todo!(),
            _ => false,
        };

        result
            && match (&self.ty, &other.ty) {
                (None, None) => true,
                (Some(left), Some(right)) => left.eq_ignoring_provenance(right),
                _ => false,
            }
    }
}

impl ListSexpr for Expr {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(
        db: &dyn SexprParser,
        source: Source,
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
            let expr_contents =
                ListSexprWrapper::<ExprContents>::parse(db, source, args.remove(0))?;
            let expr = Expr::new_in_sexpr(source, span, expr_contents);
            // for info in args {
            //     ctx.process_expr_info(db, &expr, info)?;
            // }
            Ok(expr)
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(db, source, span.clone(), args)
                .map(|expr_contents| Expr::new_in_sexpr(source, span, expr_contents))
        }
    }

    fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
        // let mut infos = ctx.process_expr_info(db, self, ctx);
        // if infos.is_empty() {
        self.contents.serialise(db)
        // } else {
        //     infos.insert(
        //         0,
        //         ListSexprWrapper::serialise_into_node(db, &self.contents),
        //     );
        //     infos.insert(
        //         0,
        //         AtomicSexprWrapper::serialise_into_node(db, &"expr".to_string()),
        //     );
        //     infos
        // }
    }
}
