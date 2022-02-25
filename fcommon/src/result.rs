use crate::{Path, Source, Span};

/// An message to be displayed to the user, such as an error or warning.
/// Rendered and displayed using the `ariadne` crate if printed to the user,
/// and converted to other diagnostic types if using the LSP protocol.
///
/// This struct is intentionally similar to the `Report` type in `ariadne`,
/// but its fields are accessible, and more closely tied to feather's internals.
/// This allows us to render a report to several different backends, including
/// `ariadne` itself, of course.
#[derive(Debug, Clone)]
pub struct Report {
    /// The severity of the diagnostic.
    /// Used to determine colouring of output if rendered using `ariadne`.
    severity: Severity,
    /// The source file that the diagnostic comes from.
    source: Source,
    /// The location in the source file at which the diagnostic originates.
    /// If the span is not specified, then the diagnostic refers to the entire file.
    offset: Option<usize>,
    /// The message to display to the user, if present.
    message: Option<String>,
    /// A final note to display to the user, if present.
    note: Option<String>,
    /// A list of labels with additional information to display to the user.
    labels: Vec<Label>,
}

impl Report {
    pub fn in_file(severity: Severity, source: Source) -> Self {
        Self {
            severity,
            source,
            offset: None,
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }

    pub fn at(severity: Severity, source: Source, offset: usize) -> Self {
        Self {
            severity,
            source,
            offset: Some(offset),
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }
}

/// <https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-levels>
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

/// A localised message in a report.
/// See the `ariadne` crate for more information.
#[derive(Debug, Clone)]
pub struct Label {
    span: Span,
    message: Option<String>,
    ty: LabelType,
    order: i32,
    priority: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelType {
    Label,
    Help,
    Note,
}

/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
#[derive(Debug)]
#[must_use = "errors must be processed by an ErrorEmitter"]
pub struct DiagnosticResult<T> {
    /// If this is `None`, then the computation failed. Error messages will be contained inside `reports`.
    /// If this is `Some`, then the computation succeeded, but there may still be some messages (e.g. warnings
    /// or errors) inside `messages`.
    value: Option<T>,
    reports: Vec<Report>,
}

impl<T> From<T> for DiagnosticResult<T> {
    fn from(value: T) -> Self {
        Self::ok(value)
    }
}

impl<T> From<Result<T, Report>> for DiagnosticResult<T> {
    fn from(result: Result<T, Report>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(error) => Self::fail(error),
        }
    }
}

impl<T> From<Result<T, Vec<Report>>> for DiagnosticResult<T> {
    fn from(result: Result<T, Vec<Report>>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(errors) => Self::fail_many(errors),
        }
    }
}

impl<T> DiagnosticResult<T> {
    /// The computation succeeded with no messages.
    /// This is the monadic `return` operation.
    pub fn ok(value: T) -> Self {
        Self {
            value: Some(value),
            reports: Vec::new(),
        }
    }

    /// The computation succeeded, but there was some error or warning message.
    pub fn ok_with(value: T, report: Report) -> Self {
        Self {
            value: Some(value),
            reports: vec![report],
        }
    }

    pub fn ok_with_many(value: T, reports: Vec<Report>) -> Self {
        Self {
            value: Some(value),
            reports,
        }
    }

    /// The computation failed. An error message is mandatory if the computation failed.
    pub fn fail(report: Report) -> Self {
        assert!(report.severity == Severity::Error);
        Self {
            value: None,
            reports: vec![report],
        }
    }

    pub fn fail_many(reports: Vec<Report>) -> Self {
        assert!(reports.iter().any(|m| m.severity == Severity::Error));
        Self {
            value: None,
            reports,
        }
    }

    /// Apply an infallible operation to the value inside this result. If the operation could fail, use [`DiagnosticResult::bind`] instead.
    pub fn map<F, U>(self, f: F) -> DiagnosticResult<U>
    where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => DiagnosticResult {
                value: Some(f(value)),
                reports: self.reports,
            },
            None => DiagnosticResult {
                value: None,
                reports: self.reports,
            },
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> DiagnosticResult<U>
    where
        F: FnOnce(T) -> DiagnosticResult<U>,
    {
        match self.value {
            Some(value) => {
                let mut result = f(value);
                self.reports.append(&mut result.reports);
                DiagnosticResult {
                    value: result.value,
                    reports: self.reports,
                }
            }
            None => DiagnosticResult {
                value: None,
                reports: self.reports,
            },
        }
    }

    /// Appends a report to this diagnostic result, regardless of whether the result succeeded or failed.
    pub fn with(mut self, report: Report) -> Self {
        self.reports.push(report);
        self
    }

    /// Converts a failed diagnostic into a successful diagnostic by wrapping
    /// the contained value in an `Option`.
    pub fn unfail(self) -> DiagnosticResult<Option<T>> {
        DiagnosticResult {
            value: Some(self.value),
            reports: self.reports,
        }
    }

    /// Converts a successful diagnostic that had one or more `Error` reports into a failed diagnostic (with the same reports).
    /// Diagnostics without `Error` reports are unaffected.
    pub fn deny(self) -> Self {
        if self.reports.iter().any(|m| m.severity == Severity::Error) {
            Self {
                value: None,
                reports: self.reports,
            }
        } else {
            self
        }
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    pub fn sequence(
        results: impl IntoIterator<Item = DiagnosticResult<T>>,
    ) -> DiagnosticResult<Vec<T>> {
        results
            .into_iter()
            .fold(DiagnosticResult::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.bind(|i| {
                        list.push(i);
                        DiagnosticResult::ok(list)
                    })
                })
            })
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    pub fn sequence_unfail(
        results: impl IntoIterator<Item = DiagnosticResult<T>>,
    ) -> DiagnosticResult<Vec<T>> {
        results
            .into_iter()
            .fold(DiagnosticResult::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.unfail().bind(|i| {
                        if let Some(i) = i {
                            list.push(i);
                        }
                        DiagnosticResult::ok(list)
                    })
                })
            })
    }

    /// Returns true if the computation succeeded.
    pub fn succeeded(&self) -> bool {
        self.value.is_some()
    }

    /// Returns true if the computation failed.
    pub fn failed(&self) -> bool {
        self.value.is_none()
    }

    /// Splits up this diagnostic result into its value and its error messages.
    /// It is your responsibility to put these error messages back inside another diagnostic result.
    /// Failure to do so will result in errors not being displayed, or invalid programs erroneously
    /// being considered correct.
    pub fn destructure(self) -> (Option<T>, Vec<Report>) {
        (self.value, self.reports)
    }

    /// Retrieves the value for inspection.
    pub fn value(&self) -> &Option<T> {
        &self.value
    }
}

impl<T> FromIterator<DiagnosticResult<T>> for DiagnosticResult<Vec<T>> {
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    fn from_iter<U: IntoIterator<Item = DiagnosticResult<T>>>(iter: U) -> Self {
        DiagnosticResult::sequence_unfail(iter)
    }
}
