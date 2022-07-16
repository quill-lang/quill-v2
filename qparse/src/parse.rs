use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
};

use fcommon::{Dr, Intern, Label, LabelType, Report, ReportKind, Source, Span};
use fnodes::{
    basic_nodes::{Name, Provenance, QualifiedName},
    expr::BinderAnnotation,
};

use crate::pre_lex::PreToken;

/// A token in the source file. One or more of these is created for each pre-token,
/// except non-documentation comment pre-tokens, which are removed.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Token {
    Lexical {
        text: String,
    },
    Operator {
        text: String,
        info: OperatorInfo,
    },
    /// `::`
    Scope,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `:`
    Type,
    /// `=`
    Assign,
    /// `,`
    Comma,
    /// `|`
    Pipe,
    /// `&`
    Borrow,
    /// `borrowed`. Represents the type of borrowed values, not the borrowed values themselves.
    Borrowed,
    /// `def`
    Def,
    /// `inductive`
    Inductive,
    /// `fn`
    Fn,
    /// `forall`
    Forall,
    /// `let`
    Let,
    /// `Sort`
    Sort,
    /// `Region`
    Region,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OperatorInfo {
    Prefix {
        precedence: i32,
    },
    Infix {
        left_precedence: i32,
        right_precedence: i32,
    },
    Postfix {
        precedence: i32,
    },
}

impl Token {
    /// Gets the amount of Unicode characters in the underlying string.
    fn chars_count(&self) -> usize {
        match self {
            Token::Lexical { text } => text.chars().count(),
            Token::Operator { text, .. } => text.chars().count(),
            Token::Scope => 2,
            Token::LParen => 1,
            Token::RParen => 1,
            Token::LBrace => 1,
            Token::RBrace => 1,
            Token::Type => 1,
            Token::Assign => 1,
            Token::Comma => 1,
            Token::Pipe => 1,
            Token::Borrow => 1,
            Token::Borrowed => "borrowed".chars().count(),
            Token::Def => "def".chars().count(),
            Token::Inductive => "inductive".chars().count(),
            Token::Fn => "fn".chars().count(),
            Token::Forall => "forall".chars().count(),
            Token::Let => "let".chars().count(),
            Token::Sort => "sort".chars().count(),
            Token::Region => "region".chars().count(),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Lexical { text } => write!(f, "\"{}\"", text),
            Token::Operator { text, .. } => write!(f, "operator \"{}\"", text),
            Token::Scope => write!(f, "'::'"),
            Token::LParen => write!(f, "'('"),
            Token::RParen => write!(f, "')'"),
            Token::LBrace => write!(f, "'{{'"),
            Token::RBrace => write!(f, "'}}'"),
            Token::Type => write!(f, "':'"),
            Token::Assign => write!(f, "'='"),
            Token::Comma => write!(f, "','"),
            Token::Pipe => write!(f, "'|'"),
            Token::Borrow => write!(f, "'&'"),
            Token::Borrowed => write!(f, "'borrowed'"),
            Token::Def => write!(f, "'def'"),
            Token::Inductive => write!(f, "'inductive'"),
            Token::Fn => write!(f, "'fn'"),
            Token::Forall => write!(f, "'forall'"),
            Token::Let => write!(f, "'let'"),
            Token::Sort => write!(f, "'Sort'"),
            Token::Region => write!(f, "'Region'"),
        }
    }
}

/// Converts a stream of pre-tokens into a stream of tokens.
/// TODO: Add functionality that allows this iterator to be given operators that it can then parse.
pub struct TokenIterator<I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    pre_tokens: I,
    /// If we just parsed a pre-token, this list is filled up with the tokens that the pre-token
    /// split up into, so that we can return them later with calls to [`Iterator::next()`].
    /// The list is reversed so [`Vec::pop()`] can be used to get the next token.
    parsed_tokens_rev: Vec<(Token, Span)>,
    /// The map of known operators to this token iterator.
    /// The innermost map converts operators as strings into their information.
    /// The outermost map tracks the size of each operator; in particular, an operator with string
    /// `s` should be stored in `operators[s.len()][s]`. This allows us to parse longer operators
    /// first, which deals with situations like favouring `++` over `+`. The structure [`BTreeMap`]
    /// is used for determinism.
    operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>>,
    /// Used for emitting diagnostics at the end of the file.
    /// When a token is emitted using `next`, its span is stored here.
    last_token: Span,
}

impl<I> TokenIterator<I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    pub fn new(pre_tokens: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            pre_tokens: pre_tokens.into_iter(),
            parsed_tokens_rev: Vec::new(),
            operators: BTreeMap::new(),
            last_token: 0..1,
        }
    }

    /// Undoes an invocation to [`Iterator::next`].
    /// This is implemented in place of any kind of "peekable" trait.
    fn push(&mut self, token: Token, span: Span) {
        self.parsed_tokens_rev.push((token, span))
    }

    fn split_pre_token(&self, text: &str, span: Span) -> Vec<(Token, Span)> {
        // Search for known operators, longest first.
        for (_, operators) in self.operators.iter().rev() {
            for (operator, info) in operators {
                if let Some((before, after)) = text.split_once(operator) {
                    // We found an operator.
                    return self.split_pre_token_recursive(
                        before,
                        after,
                        Token::Operator {
                            text: operator.clone(),
                            info: *info,
                        },
                        span,
                    );
                }
            }
        }

        // We didn't find any operators in this text.
        // Now search for important tokens like left and right parentheses.
        if let Some((before, after)) = text.split_once("::") {
            self.split_pre_token_recursive(before, after, Token::Scope, span)
        } else if let Some((before, after)) = text.split_once('(') {
            self.split_pre_token_recursive(before, after, Token::LParen, span)
        } else if let Some((before, after)) = text.split_once(')') {
            self.split_pre_token_recursive(before, after, Token::RParen, span)
        } else if let Some((before, after)) = text.split_once('{') {
            self.split_pre_token_recursive(before, after, Token::LBrace, span)
        } else if let Some((before, after)) = text.split_once('}') {
            self.split_pre_token_recursive(before, after, Token::RBrace, span)
        } else if let Some((before, after)) = text.split_once(':') {
            self.split_pre_token_recursive(before, after, Token::Type, span)
        } else if let Some((before, after)) = text.split_once('=') {
            self.split_pre_token_recursive(before, after, Token::Assign, span)
        } else if let Some((before, after)) = text.split_once(',') {
            self.split_pre_token_recursive(before, after, Token::Comma, span)
        } else if let Some((before, after)) = text.split_once('|') {
            self.split_pre_token_recursive(before, after, Token::Pipe, span)
        } else if let Some((before, after)) = text.split_once('&') {
            self.split_pre_token_recursive(before, after, Token::Borrow, span)
        } else {
            // We didn't find any other tokens in this text.
            if text.is_empty() {
                Vec::new()
            } else {
                // Treat the text as a single token.
                // TODO: Warn the user if this doesn't look like a single token.
                vec![(
                    match text {
                        "borrowed" => Token::Borrowed,
                        "def" => Token::Def,
                        "inductive" => Token::Inductive,
                        "fn" => Token::Fn,
                        "forall" => Token::Forall,
                        "let" => Token::Let,
                        "Sort" => Token::Sort,
                        "Region" => Token::Region,
                        _ => Token::Lexical {
                            text: text.to_owned(),
                        },
                    },
                    span,
                )]
            }
        }
    }

    /// Splits on `before` and `after`, and concatenates the results with `token` in between.
    fn split_pre_token_recursive(
        &self,
        before: &str,
        after: &str,
        token: Token,
        span: Span,
    ) -> Vec<(Token, Span)> {
        let before_len = before.chars().count();
        let token_len = token.chars_count();
        let mut result = self.split_pre_token(before, span.start..span.start + before_len);
        result.push((
            token,
            span.start + before_len..span.start + before_len + token_len,
        ));
        result.extend(self.split_pre_token(after, span.start + before_len + token_len..span.end));
        result
    }
}

impl<I> Iterator for TokenIterator<I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    type Item = (Token, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.parsed_tokens_rev.pop() {
            self.last_token = token.1.clone();
            Some(token)
        } else {
            // Consume and parse the next pre-token.
            if let Some((pre_token, span)) = self.pre_tokens.next() {
                match pre_token {
                    PreToken::Lexical { text } => {
                        self.parsed_tokens_rev = self.split_pre_token(&text, span);
                        self.parsed_tokens_rev.reverse();
                    }
                    PreToken::Comment { .. } => {
                        // Ignore comments that are not documentation comments.
                    }
                }
                self.next()
            } else {
                None
            }
        }
    }
}

/// A parsed item from the input stream.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum PItem {
    Definition { def: PDefinition },
    Inductive { ind: PInductive },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PDefinition {
    pub def_token: Span,
    pub name: Name,
    pub ty: PExpr,
    pub value: PExpr,
    pub universe_params: Vec<Name>,
}

impl Debug for PDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<pdef>")
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PInductive {
    pub inductive_token: Span,
    pub name: Name,
    pub ty: PExpr,
    pub global_params: u32,
    pub intro_rules: Vec<(Name, PExpr)>,
    pub universe_params: Vec<Name>,
}

impl Debug for PInductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<pind>")
    }
}

/// A parsed expression from the input stream.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PExpr {
    pub provenance: Provenance,
    pub contents: PExprContents,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PExprContents {
    QualifiedName {
        qualified_name: QualifiedName,
        universes: Vec<PUniverse>,
    },
    Apply {
        left: Box<PExpr>,
        right: Box<PExpr>,
    },
    UnaryOp {
        operator: String,
        operator_span: Span,
        param: Box<PExpr>,
    },
    BinaryOp {
        operator: String,
        operator_span: Span,
        left: Box<PExpr>,
        right: Box<PExpr>,
    },
    Forall {
        binder: PBinder,
        inner_expr: Box<PExpr>,
    },
    Function {
        binder: PBinder,
        inner_expr: Box<PExpr>,
    },
    Let {
        name_to_assign: Name,
        to_assign: Box<PExpr>,
        to_assign_ty: Box<PExpr>,
        body: Box<PExpr>,
    },
    Borrow {
        region: Box<PExpr>,
        value: Box<PExpr>,
    },
    Borrowed {
        region: Box<PExpr>,
        ty: Box<PExpr>,
    },
    Sort {
        universe: PUniverse,
    },
    Region,
}

/// A parsed universe from the input stream.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PUniverse {
    pub provenance: Provenance,
    pub contents: PUniverseContents,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PUniverseContents {
    Lexical { text: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PBinder {
    pub keyword: Span,
    pub binder_annotation: BinderAnnotation,
    pub name: Name,
    pub ty: Box<PExpr>,
}

/// Parses a list of items from a stream of pre-tokens.
pub(crate) fn parse_items(
    db: &dyn Intern,
    source: Source,
    stream: TokenIterator<impl Iterator<Item = (PreToken, Span)>>,
) -> Dr<Vec<(PItem, Span)>> {
    let mut parser = Parser { db, source, stream };
    parser.parse_items()
}

struct Parser<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    db: &'a dyn Intern,
    source: Source,
    stream: TokenIterator<I>,
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    fn parse_items(&mut self) -> Dr<Vec<(PItem, Span)>> {
        self.parse_item().bind(|result| {
            if let Some(result) = result {
                self.parse_items().map(|mut more_items| {
                    more_items.insert(0, result);
                    more_items
                })
            } else {
                Dr::ok(Vec::new())
            }
        })
    }

    /// Parses a single item from a stream of pre-tokens.
    /// If the stream was empty, return [`None`].
    fn parse_item(&mut self) -> Dr<Option<(PItem, Span)>> {
        match self.stream.next() {
            Some((Token::Def, span)) => self.parse_definition(span).map(Some),
            Some((Token::Inductive, span)) => self.parse_inductive(span).map(Some),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, span.start)
                    .with_message(format!("expected item, got {}", token))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("expected item here"),
                    ),
            ),
            None => Dr::ok(None),
        }
    }

    /// The keyword `def` has already been parsed.
    fn parse_definition(&mut self, def_token: Span) -> Dr<(PItem, Span)> {
        // Parse the name of the definition.
        self.parse_name().bind(|name| {
            // We might have a sequence of universe parameters `::{...}` here.
            let universe_parameters = match self.stream.next() {
                Some((Token::Scope, _)) => self
                    .parse_exact(Token::LBrace)
                    .bind(|_| self.parse_universe_parameters()),
                Some((token, span)) => {
                    self.stream.push(token, span);
                    Dr::ok(Vec::new())
                }
                None => Dr::ok(Vec::new()),
            };
            universe_parameters.bind(|universe_params| {
                self.parse_exact(Token::Type).bind(|_type_span| {
                    self.parse_expr().bind(|ty| {
                        self.parse_exact(Token::Assign).bind(|_assign_span| {
                            self.parse_expr().map(|value| {
                                let span = name.provenance.span();
                                (
                                    PItem::Definition {
                                        def: PDefinition {
                                            def_token,
                                            name,
                                            ty,
                                            value,
                                            universe_params,
                                        },
                                    },
                                    span,
                                )
                            })
                        })
                    })
                })
            })
        })
    }

    /// The keyword `inductive` has already been parsed.
    fn parse_inductive(&mut self, inductive_token: Span) -> Dr<(PItem, Span)> {
        // Parse the name of the inductive.
        self.parse_name().bind(|name| {
            // We might have a sequence of universe parameters `::{...}` here.
            let universe_parameters = match self.stream.next() {
                Some((Token::Scope, _)) => self
                    .parse_exact(Token::LBrace)
                    .bind(|_| self.parse_universe_parameters()),
                Some((token, span)) => {
                    self.stream.push(token, span);
                    Dr::ok(Vec::new())
                }
                None => Dr::ok(Vec::new()),
            };
            universe_parameters.bind(|universe_params| {
                // TODO: Find a better way to get the number of global parameters.
                self.parse_name().bind(|global_params| {
                    let global_params = match self
                        .db
                        .lookup_intern_string_data(global_params.contents)
                        .parse()
                    {
                        Ok(global_params) => Dr::ok(global_params),
                        Err(_) => todo!(),
                    };
                    global_params.bind(|global_params| {
                        self.parse_exact(Token::Type).bind(|_| {
                            self.parse_expr().bind(|ty| {
                                // Now parse the intro rules.
                                let mut intro_rules = Dr::ok(Vec::new());
                                loop {
                                    match self.stream.next() {
                                        Some((Token::Pipe, _)) => {
                                            intro_rules = intro_rules.bind(|mut intro_rules| {
                                                self.parse_intro_rule().map(|univ| {
                                                    intro_rules.push(univ);
                                                    intro_rules
                                                })
                                            });
                                        }
                                        Some((token, span)) => {
                                            self.stream.push(token, span);
                                            // This is the end of the list of intro rules.
                                            break intro_rules.map(|intro_rules| {
                                                let span = name.provenance.span();
                                                (
                                                    PItem::Inductive {
                                                        ind: PInductive {
                                                            inductive_token,
                                                            name,
                                                            ty,
                                                            global_params,
                                                            intro_rules,
                                                            universe_params,
                                                        },
                                                    },
                                                    span,
                                                )
                                            });
                                        }
                                        None => {
                                            // This is the end of the list of intro rules.
                                            break intro_rules.map(|intro_rules| {
                                                let span = name.provenance.span();
                                                (
                                                    PItem::Inductive {
                                                        ind: PInductive {
                                                            inductive_token,
                                                            name,
                                                            ty,
                                                            global_params,
                                                            intro_rules,
                                                            universe_params,
                                                        },
                                                    },
                                                    span,
                                                )
                                            });
                                        }
                                    }
                                }
                            })
                        })
                    })
                })
            })
        })
    }

    fn parse_intro_rule(&mut self) -> Dr<(Name, PExpr)> {
        self.parse_name().bind(|name| {
            self.parse_exact(Token::Type)
                .bind(|_| self.parse_expr().map(|ty| (name, ty)))
        })
    }

    fn parse_expr(&mut self) -> Dr<PExpr> {
        // Run a Pratt-style parser to parse this expression.
        self.parse_expr_with_precedence(i32::MIN)
    }

    /// Parses an expression with a minimum precedence.
    /// If any operator with higher precedence is met, that is not considered part of this parsed expression.
    fn parse_expr_with_precedence(&mut self, min_precedence: i32) -> Dr<PExpr> {
        let mut lhs = match self.stream.next() {
            Some((Token::Lexical { text }, span)) => self
                .parse_qualified_name(Name {
                    provenance: Provenance::Quill {
                        source: self.source,
                        span,
                    },
                    contents: self.db.intern_string_data(text),
                })
                .map(|(qualified_name, universes)| PExpr {
                    provenance: qualified_name.provenance.clone(),
                    contents: PExprContents::QualifiedName {
                        qualified_name,
                        universes,
                    },
                }),
            Some((Token::LParen, lparen_span)) => self.parse_expr().bind(|expr| {
                self.parse_exact(Token::RParen).map(|rparen_span| PExpr {
                    provenance: Provenance::Quill {
                        source: self.source,
                        span: lparen_span.start..rparen_span.end,
                    },
                    contents: expr.contents,
                })
            }),
            Some((Token::Fn, fn_span)) => {
                // Parse a binder, then parse the resulting expression.
                self.parse_binder(fn_span.clone()).bind(|binder| {
                    self.parse_exact(Token::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|inner_expr| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: fn_span.start..inner_expr.provenance.span().end,
                                },
                                contents: PExprContents::Function {
                                    binder,
                                    inner_expr: Box::new(inner_expr),
                                },
                            })
                    })
                })
            }
            Some((Token::Forall, forall_span)) => {
                // Parse a binder, then parse the resulting expression.
                self.parse_binder(forall_span.clone()).bind(|binder| {
                    self.parse_exact(Token::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|inner_expr| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: forall_span.start..inner_expr.provenance.span().end,
                                },
                                contents: PExprContents::Forall {
                                    binder,
                                    inner_expr: Box::new(inner_expr),
                                },
                            })
                    })
                })
            }
            Some((Token::Let, let_span)) => {
                // Parse the name, then parse the value we're assigning, then parse the resulting expression.
                // The structure is `let a : b = c, d`.
                self.parse_name().bind(|name_to_assign| {
                    self.parse_exact(Token::Type).bind(|_| {
                        self.parse_expr().bind(|to_assign_ty| {
                            self.parse_exact(Token::Assign).bind(|_| {
                                self.parse_expr().bind(|to_assign| {
                                    self.parse_exact(Token::Comma).bind(|_| {
                                        self.parse_expr().map(|body| PExpr {
                                            provenance: Provenance::Quill {
                                                source: self.source,
                                                span: let_span.start..body.provenance.span().end,
                                            },
                                            contents: PExprContents::Let {
                                                name_to_assign,
                                                to_assign: Box::new(to_assign),
                                                to_assign_ty: Box::new(to_assign_ty),
                                                body: Box::new(body),
                                            },
                                        })
                                    })
                                })
                            })
                        })
                    })
                })
            }
            Some((Token::Borrow, borrow_span)) => {
                // Parse a region, then parse the value to borrow.
                self.parse_expr().bind(|region| {
                    self.parse_exact(Token::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|value| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: borrow_span.start..value.provenance.span().end,
                                },
                                contents: PExprContents::Borrow {
                                    region: Box::new(region),
                                    value: Box::new(value),
                                },
                            })
                    })
                })
            }
            Some((Token::Borrowed, borrow_span)) => {
                // Parse a region, then parse the type that is to be borrowed.
                self.parse_expr().bind(|region| {
                    self.parse_exact(Token::Comma).bind(|_comma_span| {
                        self.parse_expr_with_precedence(min_precedence)
                            .map(|ty| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: borrow_span.start..ty.provenance.span().end,
                                },
                                contents: PExprContents::Borrowed {
                                    region: Box::new(region),
                                    ty: Box::new(ty),
                                },
                            })
                    })
                })
            }
            Some((Token::Sort, span)) => self.parse_universe(false).map(|universe| PExpr {
                provenance: Provenance::Quill {
                    source: self.source,
                    span: span.start..universe.provenance.span().end,
                },
                contents: PExprContents::Sort { universe },
            }),
            Some((Token::Region, span)) => Dr::ok(PExpr {
                provenance: Provenance::Quill {
                    source: self.source,
                    span,
                },
                contents: PExprContents::Region,
            }),
            Some((
                Token::Operator {
                    text,
                    info: OperatorInfo::Prefix { precedence },
                },
                span,
            )) => self
                .parse_expr_with_precedence(precedence)
                .map(|rhs| PExpr {
                    provenance: Provenance::Quill {
                        source: self.source,
                        span: span.start..rhs.provenance.span().end,
                    },
                    contents: PExprContents::UnaryOp {
                        operator: text,
                        operator_span: span,
                        param: Box::new(rhs),
                    },
                }),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, span.start)
                    .with_message(format!("expected expression, got {}", token))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("unexpected token found here"),
                    ),
            ),
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message("end of file reached, but expected an expression")
                    .with_label(
                        Label::new(
                            self.source,
                            self.stream.last_token.clone(),
                            LabelType::Error,
                        )
                        .with_message("end of file reached here"),
                    ),
            ),
        };

        loop {
            match self.stream.next() {
                Some((Token::Lexical { text }, span)) => {
                    lhs = lhs.bind(|lhs| {
                        self.parse_qualified_name(Name {
                            provenance: Provenance::Quill {
                                source: self.source,
                                span: span.clone(),
                            },
                            contents: self.db.intern_string_data(text),
                        })
                        .map(|(qualified_name, universes)| PExpr {
                            provenance: Provenance::Quill {
                                source: self.source,
                                span: lhs.provenance.span().start
                                    ..qualified_name.provenance.span().end,
                            },
                            contents: PExprContents::Apply {
                                left: Box::new(lhs),
                                right: Box::new(PExpr {
                                    provenance: qualified_name.provenance.clone(),
                                    contents: PExprContents::QualifiedName {
                                        qualified_name,
                                        universes,
                                    },
                                }),
                            },
                        })
                    });
                }
                Some((Token::LParen, lparen_span)) => {
                    lhs = lhs.bind(|lhs| {
                        self.parse_expr().bind(|rhs| {
                            self.parse_exact(Token::RParen).map(|rparen_span| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: lhs.provenance.span().start..rparen_span.end,
                                },
                                contents: PExprContents::Apply {
                                    left: Box::new(lhs),
                                    right: Box::new(PExpr {
                                        provenance: Provenance::Quill {
                                            source: self.source,
                                            span: lparen_span.start..rparen_span.end,
                                        },
                                        contents: rhs.contents,
                                    }),
                                },
                            })
                        })
                    });
                }
                Some((
                    Token::Operator {
                        text,
                        info: OperatorInfo::Postfix { precedence },
                    },
                    span,
                )) => {
                    if precedence < min_precedence {
                        self.stream.push(
                            Token::Operator {
                                text,
                                info: OperatorInfo::Postfix { precedence },
                            },
                            span,
                        );
                        break;
                    }

                    lhs = lhs.map(|lhs| PExpr {
                        provenance: Provenance::Quill {
                            source: self.source,
                            span: lhs.provenance.span().start..span.end,
                        },
                        contents: PExprContents::UnaryOp {
                            operator: text,
                            operator_span: span,
                            param: Box::new(lhs),
                        },
                    });
                }
                Some((
                    Token::Operator {
                        text,
                        info:
                            OperatorInfo::Infix {
                                left_precedence,
                                right_precedence,
                            },
                    },
                    span,
                )) => {
                    if left_precedence < min_precedence {
                        self.stream.push(
                            Token::Operator {
                                text,
                                info: OperatorInfo::Infix {
                                    left_precedence,
                                    right_precedence,
                                },
                            },
                            span,
                        );
                        break;
                    }
                    lhs = lhs.bind(|lhs| {
                        self.parse_expr_with_precedence(right_precedence)
                            .map(|rhs| PExpr {
                                provenance: Provenance::Quill {
                                    source: self.source,
                                    span: lhs.provenance.span().start..rhs.provenance.span().end,
                                },
                                contents: PExprContents::BinaryOp {
                                    operator: text,
                                    operator_span: span,
                                    left: Box::new(lhs),
                                    right: Box::new(rhs),
                                },
                            })
                    })
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    break;
                }
                None => break,
            }
        }

        lhs
    }

    fn parse_binder(&mut self, keyword: Span) -> Dr<PBinder> {
        self.parse_exact(Token::LParen).bind(|lparen_span| {
            self.parse_name().bind(|name| {
                self.parse_exact(Token::Type).bind(|ty_span| {
                    self.parse_expr().bind(|ty| {
                        self.parse_exact(Token::RParen).map(|rparen_span| PBinder {
                            keyword,
                            binder_annotation: BinderAnnotation::Explicit,
                            name,
                            ty: Box::new(ty),
                        })
                    })
                })
            })
        })
    }

    /// Parses a universe from the input stream. If `parenthesised` is true, we allow expressions
    /// such as `u + k` and `max u v` which can only be parsed when inside a set of parentheses.
    fn parse_universe(&mut self, parenthesised: bool) -> Dr<PUniverse> {
        match self.stream.next() {
            Some((Token::Lexical { text }, span)) => match text.as_str() {
                "max" => todo!(),
                "imax" => todo!(),
                _ => Dr::ok(PUniverse {
                    provenance: Provenance::Quill {
                        source: self.source,
                        span,
                    },
                    contents: PUniverseContents::Lexical { text },
                }),
            },
            Some((Token::LParen, lparen_span)) => self.parse_universe(true).bind(|univ| {
                self.parse_exact(Token::RParen)
                    .map(|rparen_span| PUniverse {
                        provenance: Provenance::Quill {
                            source: self.source,
                            span: lparen_span.start..rparen_span.end,
                        },
                        contents: univ.contents,
                    })
            }),
            _ => todo!(),
        }
    }

    /// Parses a qualified name with the given initial token.
    /// If universe parameters were provided to this qualified name, return them as well.
    fn parse_qualified_name(&mut self, initial: Name) -> Dr<(QualifiedName, Vec<PUniverse>)> {
        match self.stream.next() {
            Some((Token::Scope, _)) => {
                // What follows should either be more name segments or a `{` to start a sequence of universe parameters.
                match self.stream.next() {
                    Some((Token::Lexical { text }, span)) => self
                        .parse_qualified_name(Name {
                            provenance: Provenance::Quill {
                                source: self.source,
                                span,
                            },
                            contents: self.db.intern_string_data(text),
                        })
                        .map(|(mut name, universes)| {
                            name.provenance = Provenance::Quill {
                                source: self.source,
                                span: initial.provenance.span().start..name.provenance.span().end,
                            };
                            name.segments.insert(0, initial);
                            (name, universes)
                        }),
                    Some((Token::LBrace, span)) => {
                        // This is a sequence of universe parameters.
                        self.parse_universes().map(|(universes, rbrace_span)| {
                            (
                                QualifiedName {
                                    provenance: Provenance::Quill {
                                        source: self.source,
                                        span: initial.provenance.span().start..rbrace_span.end,
                                    },
                                    segments: vec![initial],
                                },
                                universes,
                            )
                        })
                    }
                    Some((token, span)) => Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message(format!(
                                "expected a name segment or '{{' for this qualified name, got {}",
                                token
                            ))
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token.clone(),
                                    LabelType::Error,
                                )
                                .with_message("unexpected token found here"),
                            ),
                    ),
                    None => Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message(
                                "end of file reached, but this qualified name was not complete",
                            )
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token.clone(),
                                    LabelType::Error,
                                )
                                .with_message("end of file reached here"),
                            ),
                    ),
                }
            }
            Some((token, span)) => {
                self.stream.push(token, span);
                Dr::ok((
                    QualifiedName {
                        provenance: initial.provenance.clone(),
                        segments: vec![initial],
                    },
                    Vec::new(),
                ))
            }
            None => Dr::ok((
                QualifiedName {
                    provenance: initial.provenance.clone(),
                    segments: vec![initial],
                },
                Vec::new(),
            )),
        }
    }

    /// The initial brace `{` is assumed to have been parsed.
    /// The final brace is returned as a [`Span`].
    fn parse_universes(&mut self) -> Dr<(Vec<PUniverse>, Span)> {
        let mut universes = Dr::ok(Vec::new());
        loop {
            match self.stream.next() {
                Some((Token::RBrace, span)) => {
                    // This is the end of the list of universe parameters.
                    break universes.map(|universes| (universes, span));
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    universes = universes.bind(|mut universes| {
                        self.parse_universe(false).map(|univ| {
                            universes.push(univ);
                            universes
                        })
                    });
                }
                None => {
                    break Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message("end of file reached, but expected a universe")
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token.clone(),
                                    LabelType::Error,
                                )
                                .with_message("end of file reached here"),
                            ),
                    )
                }
            }
        }
    }

    /// The initial brace `{` is assumed to have been parsed.
    fn parse_universe_parameters(&mut self) -> Dr<Vec<Name>> {
        let mut universe_parameters = Dr::ok(Vec::new());
        loop {
            match self.stream.next() {
                Some((Token::RBrace, span)) => {
                    // This is the end of the list of universe parameters.
                    break universe_parameters;
                }
                Some((token, span)) => {
                    self.stream.push(token, span);
                    universe_parameters = universe_parameters.bind(|mut universes| {
                        self.parse_name().map(|name| {
                            universes.push(name);
                            universes
                        })
                    });
                }
                None => {
                    break Dr::fail(
                        Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                            .with_message("end of file reached, but expected a universe")
                            .with_label(
                                Label::new(
                                    self.source,
                                    self.stream.last_token.clone(),
                                    LabelType::Error,
                                )
                                .with_message("end of file reached here"),
                            ),
                    )
                }
            }
        }
    }

    fn parse_name(&mut self) -> Dr<Name> {
        match self.stream.next() {
            Some((Token::Lexical { text }, span)) => Dr::ok(Name {
                provenance: Provenance::Quill {
                    source: self.source,
                    span,
                },
                contents: self.db.intern_string_data(text),
            }),
            Some((token, span)) => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message(format!("expected a name, got {}", token))
                    .with_label(
                        Label::new(self.source, span, LabelType::Error)
                            .with_message("unexpected token found here"),
                    ),
            ),
            None => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message("end of file reached, but expected a name")
                    .with_label(
                        Label::new(
                            self.source,
                            self.stream.last_token.clone(),
                            LabelType::Error,
                        )
                        .with_message("end of file reached here"),
                    ),
            ),
        }
    }

    fn parse_exact(&mut self, token: Token) -> Dr<Span> {
        match self.stream.next() {
            Some((other_token, span)) => {
                if token == other_token {
                    Dr::ok(span)
                } else {
                    Dr::ok_with(
                        span.clone(),
                        Report::new(ReportKind::Error, self.source, span.start)
                            .with_message(format!("expected {}, got {}", token, other_token))
                            .with_label(
                                Label::new(self.source, span, LabelType::Error)
                                    .with_message("unexpected token found here"),
                            ),
                    )
                }
            }
            _ => Dr::fail(
                Report::new(ReportKind::Error, self.source, self.stream.last_token.start)
                    .with_message(format!("end of file reached, but expected {}", token))
                    .with_label(
                        Label::new(
                            self.source,
                            self.stream.last_token.clone(),
                            LabelType::Error,
                        )
                        .with_message("end of file reached here"),
                    ),
            ),
        }
    }
}
