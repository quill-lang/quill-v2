use std::collections::HashMap;

use fcommon::Span;
use fcommon::{FileReader, Source};
use fnodes::basic_nodes::QualifiedName;
use lsp_types::{SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokensLegend};
use qdb::QuillDatabase;
use qparse::*;

#[derive(Debug)]
struct RawSemanticToken {
    pub span: Span,
    pub token_type: u32,
    pub token_modifiers_bitset: u32,
}

struct SemanticTokenGenerator<'a> {
    db: &'a QuillDatabase,
    source: Source,
    /// The char indices at which '\n' characters appear in the source.
    line_breaks: Vec<usize>,
    tokens: Vec<RawSemanticToken>,
}

impl<'a> SemanticTokenGenerator<'a> {
    fn finish(mut self) -> Vec<SemanticToken> {
        self.tokens
            .sort_by(|l, r| usize::cmp(&l.span.start, &r.span.start));
        let mut result = Vec::new();
        let mut line = 0;
        let mut col = 0;
        for token in self.tokens {
            let token_line = self
                .line_breaks
                .partition_point(|&index| index < token.span.start);
            let token_col = token.span.start
                - if token_line == 0 {
                    0
                } else {
                    self.line_breaks[token_line - 1] + 1
                };
            result.push(SemanticToken {
                delta_line: (token_line - line) as u32,
                delta_start: if line == token_line {
                    (token_col - col) as u32
                } else {
                    token_col as u32
                },
                length: (token.span.end - token.span.start) as u32,
                token_type: token.token_type,
                token_modifiers_bitset: token.token_modifiers_bitset,
            });
            line = token_line;
            col = token_col;
        }
        result
    }

    fn push_token(&mut self, span: Span, token_type: u32, token_modifiers_bitset: u32) {
        self.tokens.push(RawSemanticToken {
            span,
            token_type,
            token_modifiers_bitset,
        });
    }

    fn gen(&mut self) {
        let parsed = self.db.parse_quill(self.source);
        if let Some(parsed) = parsed.value() {
            for (item, span) in parsed.as_ref() {
                match item {
                    PItem::Definition { def } => {
                        self.gen_definition(def);
                    }
                    PItem::Inductive { ind } => {
                        self.gen_inductive(ind);
                    }
                }
            }
        }
    }

    fn gen_definition(&mut self, def: &PDefinition) {
        self.push_token(
            def.def_token.clone(),
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::KEYWORD],
            0,
        );
        self.push_token(
            def.name.provenance.span(),
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::FUNCTION],
            0,
        );
        self.gen_expr(&def.ty);
        self.gen_expr(&def.value);
    }

    fn gen_inductive(&mut self, ind: &PInductive) {
        self.push_token(
            ind.inductive_token.clone(),
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::KEYWORD],
            0,
        );
        self.push_token(
            ind.name.provenance.span(),
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::STRUCT],
            0,
        );
    }

    fn gen_expr(&mut self, e: &PExpr) {
        match &e.contents {
            PExprContents::QualifiedName {
                qualified_name,
                universes,
            } => {
                self.gen_qualified_name(qualified_name);
            }
            PExprContents::Apply { left, right } => {
                self.gen_expr(left);
                self.gen_expr(right);
            }
            PExprContents::UnaryOp {
                operator,
                operator_span,
                param,
            } => {
                self.gen_expr(param);
            }
            PExprContents::BinaryOp {
                operator,
                operator_span,
                left,
                right,
            } => {
                self.gen_expr(left);
                self.gen_expr(right);
            }
            PExprContents::Forall { binder, inner_expr } => {
                self.push_token(
                    binder.name.provenance.span(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::VARIABLE],
                    0,
                );
                self.gen_expr(&binder.ty);
                self.gen_expr(inner_expr);
            }
            PExprContents::Function { binder, inner_expr } => {
                self.push_token(
                    binder.name.provenance.span(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::VARIABLE],
                    0,
                );
                self.gen_expr(&binder.ty);
                self.gen_expr(inner_expr);
            }
            PExprContents::Let {
                name_to_assign,
                to_assign,
                to_assign_ty,
                body,
            } => {}
            PExprContents::Sort { universe } => {}
        }
    }

    fn gen_qualified_name(&mut self, qualified_name: &QualifiedName) {
        // self.push_token(
        //     qualified_name.provenance.span(),
        //     SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::FUNCTION],
        //     0,
        // );
    }
}

pub fn create_semantic_tokens(db: &QuillDatabase, source: Source) -> Vec<SemanticToken> {
    let file_contents = db.source(source);
    let mut gen = SemanticTokenGenerator {
        db,
        source,
        tokens: Vec::new(),
        line_breaks: if let Some(file_contents) = file_contents.value() {
            file_contents
                .chars()
                .enumerate()
                .filter(|(_, c)| *c == '\n')
                .map(|(i, _)| i)
                .collect()
        } else {
            return Vec::new();
        },
    };
    gen.gen();
    gen.finish()
}

pub fn semantic_tokens_legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: SEMANTIC_TOKEN_LEGEND_VEC.clone(),
        token_modifiers: vec![SemanticTokenModifier::DEFINITION],
    }
}

lazy_static::lazy_static! {
    static ref SEMANTIC_TOKEN_LEGEND_VEC: Vec<SemanticTokenType> = {
        vec![
            SemanticTokenType::FUNCTION,
            SemanticTokenType::STRUCT,
            SemanticTokenType::KEYWORD,
            SemanticTokenType::VARIABLE,
        ]
    };
    static ref SEMANTIC_TOKEN_LEGEND: HashMap<SemanticTokenType, u32> = {
        let mut m = HashMap::new();
        for (i, value) in SEMANTIC_TOKEN_LEGEND_VEC.iter().enumerate() {
            m.insert(value.clone(), i as u32);
        }
        m
    };
}
