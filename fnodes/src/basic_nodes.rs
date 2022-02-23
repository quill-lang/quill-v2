use crate::*;

impl SexprListParsable for Span {
    const KEYWORD: Option<&'static str> = None;

    fn parse_list(span: Span, args: Vec<SexprNode>) -> Result<Self, ParseError> {
        let [start, end] = force_arity(span, args)?;

        // For the sake of compatibility across platforms, we enforce that spans are decoded as `u32`s first.

        let start = AtomParsableWrapper::<u32>::parse(start)?.0;
        let end = AtomParsableWrapper::<u32>::parse(end)?.0;

        Ok((start as usize)..(end as usize))
    }
}

#[cfg(test)]
mod tests {
    use chumsky::Parser;

    use super::*;

    #[test]
    fn span() {
        let pairs = [
            ("(123 324)", Ok(123..324)),
            ("(0 0)", Ok(0..0)),
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
            let actual = ListParsableWrapper::<Span>::parse(sexpr_parser().parse(string).unwrap())
                .map(|x| x.0);
            assert_eq!(actual, expected);
        }
    }
}
