use std::collections::HashMap;

use fcommon::Span;
use fcommon::{FileReader, Source};
use fnodes::basic_nodes::QualifiedName;
use lsp_types::{SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokensLegend};
use qdb::QuillDatabase;
use qparse::*;

use crate::range::RangeData;

#[derive(Debug)]
struct RawSemanticToken {
    pub span: Span,
    pub token_type: u32,
    pub token_modifiers_bitset: u32,
}

struct SemanticTokenGenerator<'a> {
    db: &'a QuillDatabase,
    source: Source,
    range_data: RangeData,
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
            let pos = self.range_data.span_position_to_position(token.span.start);
            result.push(SemanticToken {
                delta_line: (pos.line - line) as u32,
                delta_start: if line == pos.line {
                    (pos.character - col) as u32
                } else {
                    pos.character as u32
                },
                length: (token.span.end - token.span.start) as u32,
                token_type: token.token_type,
                token_modifiers_bitset: token.token_modifiers_bitset,
            });
            line = pos.line;
            col = pos.character;
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
        let parsed = self
            .db
            .source(self.source)
            .bind(|file_contents| self.db.parse_quill(self.source, file_contents));
        if let Some(parsed) = parsed.value() {
            for (item, span) in parsed.as_ref() {
                tracing::info!("span {:?}", span);
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
            PExprContents::Borrow { region, value } => {}
            PExprContents::Borrowed { region, ty } => {}
            PExprContents::Sort { universe } => {}
            PExprContents::Region => {}
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
        range_data: if let Some(file_contents) = file_contents.value() {
            RangeData::new(file_contents)
        } else {
            return Vec::new();
        },
    };
    tracing::trace!(
        "creating semantic tokens for:\n{}",
        file_contents.value().as_ref().unwrap()
    );
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
