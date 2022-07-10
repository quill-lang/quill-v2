//! A parser for Quill files. Since syntax can be extended, we cannot easily separate the parsing
//! phase on a per-file scale like many other parsers do. Instead, we must parse each *item*
//! separately, and when new notation is introduced, add this to the parser that will be used with
//! subsequent items.

mod parse;
mod pre_lex;

pub use parse::*;
use pre_lex::*;

use std::sync::Arc;

use fcommon::{Dr, FileReader, Intern, Source, Span};
use upcast::Upcast;

#[salsa::query_group(QuillParserStorage)]
pub trait QuillParser: FileReader + Upcast<dyn Intern> {
    fn parse_quill(&self, source: Source) -> Dr<Arc<Vec<(PItem, Span)>>>;
}

#[tracing::instrument(level = "debug")]
fn parse_quill(db: &dyn QuillParser, source: Source) -> Dr<Arc<Vec<(PItem, Span)>>> {
    db.source(source)
        .as_deref()
        .map(|source_code| pre_lex(source_code.chars()))
        .bind(|pre_tokens| parse_items(db.up(), source, TokenIterator::new(pre_tokens)))
        .map(Arc::new)
}
