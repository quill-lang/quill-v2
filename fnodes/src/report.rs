use std::fmt::Debug;

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::Parser;

use crate::{
    deserialise::{ListParsableWrapper, ParseErrorReason, SexprListParsable, SexprParsable},
    s_expr::sexpr_parser,
};

/// Parse this input source.
/// If errors were found, they are printed to `stdout` and `None` is returned.
///
/// TODO: Convert this into a query-style function.
/// This should only be used for testing purposes.
pub fn parse_and_report<P>(src: &str) -> Option<P>
where
    P: SexprListParsable + Debug,
{
    let s_expr = sexpr_parser().parse(src);
    let s_expr = match s_expr {
        Ok(value) => value,
        Err(errs) => {
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

                let report = Report::build(ReportKind::Error, (), e.span().start)
                    .with_message(msg)
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "unexpected {}",
                                e.found()
                                    .map(|c| format!("token {}", c.fg(Color::Red)))
                                    .unwrap_or_else(|| "end of input".to_string())
                            ))
                            .with_color(Color::Red),
                    );

                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                        .with_label(
                            Label::new(span.clone())
                                .with_message(format!(
                                    "unclosed delimiter {}",
                                    delimiter.fg(Color::Yellow)
                                ))
                                .with_color(Color::Yellow),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report,
                    chumsky::error::SimpleReason::Custom(msg) => report.with_label(
                        Label::new(e.span())
                            .with_message(format!("{}", msg.fg(Color::Yellow)))
                            .with_color(Color::Yellow),
                    ),
                };

                report.finish().print(Source::from(&src)).unwrap();
            }
            return None;
        }
    };

    let result = ListParsableWrapper::<P>::parse(s_expr).map(|x| x.0);
    match result {
        Ok(value) => Some(value),
        Err(err) => {
            let msg = match err.reason {
                ParseErrorReason::ParseIntError { text, err } => {
                    format!("couldn't parse '{}' as int: {}", text, err)
                }
                ParseErrorReason::ExpectedAtom => "expected an atom, but found a list".to_string(),
                ParseErrorReason::ExpectedList => "expected a list, but found an atom".to_string(),
                ParseErrorReason::ExpectedKeywordFoundList { expected } => {
                    format!("expected keyword '{}', but found a list", expected)
                }
                ParseErrorReason::ExpectedKeywordFoundEmpty { expected } => format!(
                    "expected keyword '{}' at the start of this list, but the list was empty",
                    expected
                ),
                ParseErrorReason::WrongKeyword { expected, found } => format!(
                    "expected keyword '{}', but found keyword '{}'",
                    expected, found
                ),
                ParseErrorReason::WrongArity {
                    expected_arity,
                    found_arity,
                } => format!(
                    "expected this list to have {} elements, but found {}",
                    expected_arity, found_arity
                ),
            };

            let report = Report::build(ReportKind::Error, (), err.span.start)
                .with_message(msg)
                .with_label(
                    Label::new(err.span)
                        .with_message("error originated here")
                        .with_color(Color::Red),
                );

            report.finish().print(Source::from(&src)).unwrap();
            None
        }
    }
}
