use crate::{deserialise::*, s_expr::*};

/// Represents a line-column pair in source code.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Location {
    /// Zero-indexed line number.
    pub line: u32,
    /// Zero-indexed column number.
    pub col: u32,
}

impl SexprListParsable for Location {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(span: Span, args: Vec<SexprNode>) -> Result<Self, ParseError> {
        let [line, col] = force_arity(span, args)?;

        let line = AtomParsableWrapper::<u32>::parse(line)?.0;
        let col = AtomParsableWrapper::<u32>::parse(col)?.0;

        Ok(Location { line, col })
    }
}

#[cfg(test)]
mod tests {
    use chumsky::Parser;

    use super::*;

    #[test]
    fn location() {
        let pairs = [
            (
                "(123 324)",
                Ok(Location {
                    line: 123,
                    col: 324,
                }),
            ),
            ("(0 0)", Ok(Location { line: 0, col: 0 })),
            (
                "(3 -45)",
                Err(ParseError {
                    span: 3..6,
                    reason: ParseErrorReason::ParseIntError {
                        text: "-45".to_string(),
                        err: "-1".parse::<u32>().unwrap_err(),
                    },
                }),
            ),
            (
                "(3 (2))",
                Err(ParseError {
                    span: 3..6,
                    reason: ParseErrorReason::ExpectedAtom,
                }),
            ),
        ];

        for (string, expected) in pairs {
            let actual =
                ListParsableWrapper::<Location>::parse(sexpr_parser().parse(string).unwrap())
                    .map(|x| x.0);
            assert_eq!(actual, expected);
        }
    }
}
