use crate::*;
use fcommon::Span;

/// Processes everything to do with every kind of expression.
/// In particular, this generates the ExprContents and PartialValue structs.
macro_rules! expr {
    ($( ( $($variant:tt)* ) )*) => {
        $(
            gen_nary!( $($variant)* );
        )*

        /// # Adding variants
        /// When adding a new variant to [`ExprContents`], make sure to update:
        /// - [`ExprContents::sub_expressions`]
        /// - [`ExprContents::sub_expressions_mut`]
        #[derive(Debug, PartialEq, Eq)]
        pub enum ExprContents {
            $( expr_contents_variant!($( $variant )*) ),*
        }

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
        pub enum PartialValue {}

        // impl ExprContents {
        //     pub fn variant_keyword(&self) -> &'static str {
        //         match self {
        //             $(
        //                 Self::$name(_) => <$path>::KEYWORD.unwrap()
        //             ),*
        //         }
        //     }
        // }

        // $(
        //     impl TryFrom<ExprContents> for $type {
        //         type Error = &'static str;
        //         fn try_from(value: ExprContents) -> Result<Self, Self::Error> {
        //             if let ExprContents::$name(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
        //         }
        //     }

        //     impl From<$type> for ExprContents {
        //         fn from(value: $type) -> ExprContents {
        //             ExprContents::$name(value)
        //         }
        //     }
        // )*

        impl ListSexpr for ExprContents {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
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
                    // $(
                    //     <$path>::KEYWORD => <$path>::parse_list(ctx, db, span, args)?.into(),
                    // )*
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

            fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
                // TODO: expr infos
                // match self {
                //     $(
                //         Self::$name(val) => {
                //             let mut result = val.serialise(ctx, db);
                //             result.insert(0, SexprNode {
                //                 contents: SexprNodeContents::Atom(<$path>::KEYWORD.unwrap().to_string()),
                //                 span: 0..0
                //             });
                //             result
                //         }
                //     ),*
                // }
                todo!()
            }
        }

        impl ListSexpr for PartialValue {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
                todo!()
            }

            fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
                todo!()
            }
        }
    };
}

macro_rules! expr_contents_variant {
    (nullary ($( _meta:tt )*) $n:ident $s:expr) => {
        $n,
    };
    () => {

    };
}

macro_rules! gen_nary {
    (nullary $( $tail:tt )*) => {
        gen_nullary!($( $tail )*);
    };
    (unary $( $tail:tt )*) => {
        gen_unary!($( $tail )*);
    };
    (binary $( $tail:tt )*) => {
        gen_binary!($( $tail )*);
    };
}

macro_rules! kwd_to_wrapper {
    (atomic) => {
        AtomicSexprWrapper<_>
    };
    (list) => {
        ListSexprWrapper<_>
    };
}

/// The type that a given type parameter expands to, if we're in a node-based expression.
macro_rules! ty_param_node {
    (E) => {
        Expr
    };
}

/// The type that a given type parameter expands to, if we're in a value-based expression.
macro_rules! ty_param_value {
    (E) => {
        PartialValue
    };
}

macro_rules! gen_nullary {
    (($($start:tt)*) $n:ident $s:expr) => {
        $($start)*
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub struct $n;

        impl ListSexpr for $n {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                _ctx: &mut SexprParseContext,
                _db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [] = force_arity(span, args)?;
                Ok(Self)
            }

            fn serialise(
                &self,
                _ctx: &SexprSerialiseContext,
                _db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                Vec::new()
            }
        }
    };
}

macro_rules! gen_unary {
    (($($start:tt)*) $n:ident($i:ident $t:ty) $s:expr) => {
        $($start)*
        #[derive(Debug, PartialEq, Eq)]
        pub struct $n(pub $t);

        impl ListSexpr for $n {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                ctx: &mut SexprParseContext,
                db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [value] = force_arity(span, args)?;
                Ok(Self(<kwd_to_wrapper!($i) as SexprParsable>::parse(ctx, db, value)?))
            }

            fn serialise(
                &self,
                ctx: &SexprSerialiseContext,
                db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                vec![<kwd_to_wrapper!($i)>::serialise_into_node(ctx, db, &self.0)]
            }
        }
    };
}

macro_rules! gen_binary {
    (($($start:tt)*) $n:ident < $($ty_param:ident),* > { $n1:ident: $i1:ident $t1:ty, $n2:ident: $i2:ident $t2:ty, } $s:expr) => {
        $($start)*
        #[derive(Debug, PartialEq, Eq)]
        pub struct $n < $($ty_param),* > {
            $n1: $t1,
            $n2: $t2,
        }

        impl ListSexpr for $n < $( ty_param_node!($ty_param) ),* > {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                ctx: &mut SexprParseContext,
                db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [v1, v2] = force_arity(span, args)?;
                Ok(Self {
                    $n1: <kwd_to_wrapper!($i1) as SexprParsable>::parse(ctx, db, v1)?,
                    $n2: <kwd_to_wrapper!($i2) as SexprParsable>::parse(ctx, db, v2)?,
                })
            }

            fn serialise(
                &self,
                ctx: &SexprSerialiseContext,
                db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                vec![
                    <kwd_to_wrapper!($i1)>::serialise_into_node(ctx, db, &self.$n1),
                    <kwd_to_wrapper!($i2)>::serialise_into_node(ctx, db, &self.$n2),
                ]
            }
        }

        impl ListSexpr for $n < $( ty_param_value!($ty_param) ),* > {
            const KEYWORD: Option<&'static str> = Some($s);

            fn parse_list(
                ctx: &mut SexprParseContext,
                db: &dyn SexprParser,
                span: Span,
                args: Vec<SexprNode>,
            ) -> Result<Self, ParseError> {
                let [v1, v2] = force_arity(span, args)?;
                Ok(Self {
                    $n1: <kwd_to_wrapper!($i1) as SexprParsable>::parse(ctx, db, v1)?,
                    $n2: <kwd_to_wrapper!($i2) as SexprParsable>::parse(ctx, db, v2)?,
                })
            }

            fn serialise(
                &self,
                ctx: &SexprSerialiseContext,
                db: &dyn SexprParser,
            ) -> Vec<SexprNode> {
                vec![
                    <kwd_to_wrapper!($i1)>::serialise_into_node(ctx, db, &self.$n1),
                    <kwd_to_wrapper!($i2)>::serialise_into_node(ctx, db, &self.$n2),
                ]
            }
        }
    };
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
                // ctx.process_expr_info(db, &expr, info)?;
            }
            Ok(expr)
        } else {
            // This is of the form `ExprContents`.
            ExprContents::parse_list(ctx, db, span.clone(), args)
                .map(|expr_contents| Node::new(ctx.node_id_gen.gen(), span, expr_contents))
        }
    }

    fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
        let mut infos = Vec::new();
        // let mut infos = ctx.process_expr_info(db, self, ctx);
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

// The following macro invocation essentially declares the entirety of
// the type state of feather expressions.

expr! {
    (nullary () IntroLocal "local")

    (unary (
        #[derive(Copy, Clone)]
    ) IntroU64(atomic u64) "iu64")

    (binary () Let<E> {
        to_assign: list Box<E>,
        body: list Box<E>,
    } "let")
}
