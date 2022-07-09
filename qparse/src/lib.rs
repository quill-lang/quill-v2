//! A parser for Quill files. Since syntax can be extended, we cannot easily separate the parsing
//! phase on a per-file scale like many other parsers do. Instead, we must parse each *item*
//! separately, and when new notation is introduced, add this to the parser that will be used with
//! subsequent items.

use std::sync::Arc;

use chumsky::{error::SimpleReason, prelude::*, stream::Stream};
use fcommon::{Dr, FileReader, Intern, Label, LabelType, Report, ReportKind, Source, Span};
use upcast::Upcast;

/// A lexical pre-token is string of input text, not enclosed in a comment or string literal, which
/// is not directly adjacent to any other non-space characters. Many of these are tokens, but some
/// pre-tokens will need to be further split up into actual tokens. For instance, `(1)` is a
/// single pre-token because it contains no spaces, but (unless `(1)` is defined as an operator
/// somewhere) it will then be converted into the tokens [`(`, `1`, `)`].
///
/// A pre-token is either a lexical pre-token or a comment token.
/// Later, we may add string and char literals as extra variants to this enum.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum PreToken {
    Lexical { text: String },
    Comment { text: String },
}

/// Splits the input stream up into pre-tokens.
fn pre_lexer() -> impl Parser<char, Vec<(PreToken, Span)>, Error = Simple<char>> {
    // A pretoken is a sequence of non-whitespace characters.
    let pretoken = filter(|c: &char| !c.is_whitespace())
        .map(Some)
        .chain::<char, Vec<_>, _>(filter(|c: &char| !c.is_whitespace()).repeated())
        .collect()
        .map_with_span(|text, span| (PreToken::Lexical { text }, span));
    let comment =
        just("//")
            .then(take_until(text::newline()))
            .map_with_span(|(_, (text, ())), span| {
                (
                    PreToken::Comment {
                        text: text.into_iter().collect(),
                    },
                    span,
                )
            });
    let block_comment =
        just("/*")
            .then(take_until(just("*/")))
            .map_with_span(|(_, (text, _)), span| {
                (
                    PreToken::Comment {
                        text: text.into_iter().collect(),
                    },
                    span,
                )
            });
    comment.or(block_comment).or(pretoken).padded().repeated()
}

pub(crate) fn parse(source: Source, source_contents: &str) -> Dr<Vec<(PreToken, Span)>> {
    match pre_lexer().parse(source_contents) {
        Ok(value) => value.into(),
        Err(errs) => {
            let mut reports = Vec::new();
            for e in errs.into_iter() {
                let msg = format!(
                    "{}{}, expected {}",
                    if e.found().is_some() {
                        "unexpected token"
                    } else {
                        "unexpected end of input"
                    },
                    if let Some(label) = e.label() {
                        format!(" while parsing {}", label)
                    } else {
                        String::new()
                    },
                    if e.expected().len() == 0 {
                        "something else".to_string()
                    } else {
                        e.expected()
                            .map(|expected| match expected {
                                Some(expected) => expected.to_string(),
                                None => "end of input".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    },
                );

                let report = Report::new(ReportKind::Error, source, e.span().start)
                    .with_message(msg)
                    .with_label(Label::new(source, e.span(), LabelType::Error).with_message(
                        format!(
                                "unexpected {}",
                                e.found()
                                    .map(|c| format!("token {}", c))
                                    .unwrap_or_else(|| "end of input".to_string())
                            ),
                    ));

                let report = match e.reason() {
                    SimpleReason::Unclosed { span, delimiter } => report.with_label(
                        Label::new(source, span.clone(), LabelType::Error)
                            .with_message(format!("unclosed delimiter {}", delimiter)),
                    ),
                    SimpleReason::Unexpected => report,
                    SimpleReason::Custom(msg) => report.with_label(
                        Label::new(source, e.span(), LabelType::Error).with_message(msg),
                    ),
                };

                reports.push(report);
            }
            Dr::fail_many(reports)
        }
    }
}

#[salsa::query_group(QuillParserStorage)]
pub trait QuillParser: FileReader + Upcast<dyn Intern> {
    fn parse_quill(&self, source: Source) -> Dr<Arc<Vec<(PreToken, Span)>>>;
}

#[tracing::instrument(level = "debug")]
fn parse_quill(db: &dyn QuillParser, source: Source) -> Dr<Arc<Vec<(PreToken, Span)>>> {
    db.source(source)
        .as_deref()
        .bind(|source_code| parse(source, source_code))
        .map(Arc::new)
}
