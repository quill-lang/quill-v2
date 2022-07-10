//! A parser for Quill files. Since syntax can be extended, we cannot easily separate the parsing
//! phase on a per-file scale like many other parsers do. Instead, we must parse each *item*
//! separately, and when new notation is introduced, add this to the parser that will be used with
//! subsequent items.

use std::sync::Arc;

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
fn pre_lex(stream: impl Iterator<Item = char>) -> Vec<(PreToken, Span)> {
    let mut stream = stream.enumerate().peekable();
    let mut result = Vec::new();
    loop {
        // Parse as much whitespace as possible.
        while let Some((_, c)) = stream.peek() {
            if c.is_whitespace() {
                stream.next();
            } else {
                break;
            }
        }

        // Parse the next pretoken from the stream.
        let mut text = String::new();
        // The start position of this pretoken.
        let start = if let Some((i, _)) = stream.peek() {
            *i
        } else {
            break;
        };
        let mut end = start;

        let pretoken = loop {
            if let Some((i, c)) = stream.next() {
                end = i;
                if c.is_whitespace() {
                    // This is the end of the pretoken.
                    break PreToken::Lexical { text };
                } else {
                    // This is still part of the pretoken.
                    text.push(c);
                    if text.len() == 2 {
                        // Check whether this is `//` or `/*`.
                        if text == "//" {
                            // Parse this pretoken as a line comment.
                            text = String::new();
                            for (i, c) in stream.by_ref() {
                                if c == '\r' || c == '\n' {
                                    break;
                                } else {
                                    text.push(c);
                                    end = i;
                                }
                            }
                            break PreToken::Comment { text };
                        }
                        // TODO: Nested block comments.
                    }
                }
            } else {
                // This is the end of the file, so the end of the pretoken.
                break PreToken::Lexical { text };
            }
        };

        result.push((pretoken, start..end));
    }

    result
}

#[salsa::query_group(QuillParserStorage)]
pub trait QuillParser: FileReader + Upcast<dyn Intern> {
    fn parse_quill(&self, source: Source) -> Dr<Arc<Vec<(PreToken, Span)>>>;
}

#[tracing::instrument(level = "debug")]
fn parse_quill(db: &dyn QuillParser, source: Source) -> Dr<Arc<Vec<(PreToken, Span)>>> {
    db.source(source)
        .as_deref()
        .map(|source_code| pre_lex(source_code.chars()))
        .map(Arc::new)
}
