//! Converts [`fcommon::Span`] into [`lsp_types::Range`].

use std::collections::HashMap;

use fcommon::{FileReader, Source, Span};
use lsp_types::{Position, Range};
use qdb::QuillDatabase;

/// Contains information about how to resolve ranges and spans in a given file.
pub struct RangeData {
    /// The char indices at which '\n' characters appear in the source.
    line_breaks: Vec<usize>,
}

impl RangeData {
    pub fn new(file_contents: &str) -> Self {
        Self {
            line_breaks: file_contents
                .chars()
                .enumerate()
                .filter(|(_, c)| *c == '\n')
                .map(|(i, _)| i)
                .collect(),
        }
    }

    /// Converts a span position (`span.start` or `span.end`) into a line-column pair.
    pub fn span_position_to_position(&self, position: usize) -> Position {
        let line = self.line_breaks.partition_point(|&index| index < position);
        let character = position as u32
            - if line == 0 {
                0
            } else {
                self.line_breaks[line - 1] as u32 + 1
            };
        Position {
            line: line as u32,
            character,
        }
    }

    pub fn span_to_range(&self, span: Span) -> Range {
        Range {
            start: self.span_position_to_position(span.start),
            end: self.span_position_to_position(span.end),
        }
    }
}

/// Contains information about how to resolve ranges and spans in a set of files.
pub struct MultiRangeData<'db> {
    /// The database we use to resolve the file contents.
    db: &'db QuillDatabase,
    range_data: HashMap<Source, RangeData>,
}

impl<'db> MultiRangeData<'db> {
    pub fn new(db: &'db QuillDatabase) -> Self {
        Self {
            db,
            range_data: HashMap::new(),
        }
    }

    /// Extracts (or generates, if it is absent) the range data for a given source file.
    pub fn range_data(&mut self, source: Source) -> &RangeData {
        self.range_data.entry(source).or_insert_with_key(|source| {
            match self.db.source(*source).value() {
                Some(file_contents) => RangeData::new(file_contents),
                // Generate dummy range data if the file could not be loaded.
                None => RangeData::new(""),
            }
        })
    }
}
