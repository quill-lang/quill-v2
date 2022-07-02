use std::ops::Deref;

use crate::{Source, Span};

/// An message to be displayed to the user, such as an error or warning.
/// Rendered and displayed using the `ariadne` crate if printed to the user,
/// and converted to other diagnostic types if using the LSP protocol.
///
/// This struct is intentionally similar to the `Report` type in `ariadne`,
/// but its fields are accessible, and more closely tied to feather's internals.
/// This allows us to render a report to several different backends, including
/// `ariadne` itself, of course.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report {
    /// The severity of the report.
    /// Used to determine colouring of output if rendered using `ariadne`.
    kind: ReportKind,
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
    pub fn new_in_file(kind: ReportKind, source: Source) -> Self {
        Self {
            kind,
            source,
            offset: None,
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }

    pub fn new(kind: ReportKind, source: Source, offset: usize) -> Self {
        Self {
            kind,
            source,
            offset: Some(offset),
            message: None,
            note: None,
            labels: Vec::new(),
        }
    }

    pub fn with_message(mut self, message: impl ToString) -> Self {
        self.message = Some(message.to_string());
        self
    }

    pub fn with_label(mut self, label: Label) -> Self {
        self.labels.push(label);
        self
    }

    pub fn with_note(mut self, note: impl ToString) -> Self {
        self.note = Some(note.to_string());
        self
    }

    /// Convert this report into an [`ariadne::Report`] and then
    /// display it to the user.
    #[cfg(feature = "ariadne")]
    pub fn render(&self, db: &impl crate::FileReader, stream: impl std::io::Write) {
        ariadne::Report::from(self)
            .write(
                FileReaderCache {
                    db,
                    files: Default::default(),
                },
                stream,
            )
            .unwrap();
    }
}

/// Holds a database and uses it as a cache for `ariadne`.
#[cfg(feature = "ariadne")]
struct FileReaderCache<'db, T>
where
    T: crate::FileReader,
{
    db: &'db T,
    files: std::collections::HashMap<Source, ariadne::Source>,
}

#[cfg(feature = "ariadne")]
impl<'db, T> ariadne::Cache<Source> for FileReaderCache<'db, T>
where
    T: crate::FileReader,
{
    fn fetch(&mut self, id: &Source) -> Result<&ariadne::Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(match self.files.entry(*id) {
            std::collections::hash_map::Entry::Occupied(occupied) => occupied.into_mut(),
            std::collections::hash_map::Entry::Vacant(vacant) => {
                vacant.insert(ariadne::Source::from(
                    self.db
                        .source(*id)
                        .value
                        .as_ref()
                        .map(|x| x.as_str())
                        .unwrap_or("<could not read file>"),
                ))
            }
        })
    }

    fn display<'a>(&self, id: &'a Source) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(
            self.db
                .path_to_path_buf(id.path)
                .with_extension(id.ty.extension())
                .to_string_lossy()
                .to_string(),
        ))
    }
}

/// Convert this report into an [`ariadne::Report`] in order
/// to display it to the user.
/// Enabled only when the `ariadne` feature flag is set.
#[cfg(feature = "ariadne")]
impl From<&Report> for ariadne::Report<(Source, Span)> {
    fn from(report: &Report) -> Self {
        let mut result = ariadne::Report::build(
            report.kind.into(),
            report.source,
            report.offset.unwrap_or(0),
        );
        if let Some(message) = &report.message {
            result = result.with_message(message);
        }
        if let Some(note) = &report.note {
            result = result.with_note(note);
        }
        for label in &report.labels {
            result = result.with_label(label.into());
        }
        result.finish()
    }
}

/// <https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-levels>
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReportKind {
    Error,
    Warning,
}

#[cfg(feature = "ariadne")]
impl From<ReportKind> for ariadne::ReportKind {
    fn from(kind: ReportKind) -> Self {
        match kind {
            ReportKind::Error => ariadne::ReportKind::Error,
            ReportKind::Warning => ariadne::ReportKind::Warning,
        }
    }
}

/// A localised message in a report.
/// See the `ariadne` crate for more information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    source: Source,
    span: Span,
    ty: LabelType,
    message: Option<String>,
    order: i32,
    priority: i32,
}

#[cfg(feature = "ariadne")]
impl From<&Label> for ariadne::Label<(Source, Span)> {
    fn from(label: &Label) -> Self {
        let mut result = Self::new((label.source, label.span.clone()))
            .with_color(label.ty.into())
            .with_order(label.order)
            .with_priority(label.priority);
        if let Some(message) = &label.message {
            result = result.with_message(message);
        }
        result
    }
}

/// Influences the colour used to display this label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelType {
    Error,
    Warning,
    Note,
}

/// Each label type is associated with a particular colour.
#[cfg(feature = "ariadne")]
impl From<LabelType> for ariadne::Color {
    fn from(ty: LabelType) -> Self {
        match ty {
            LabelType::Error => Self::Red,
            LabelType::Warning => Self::Yellow,
            LabelType::Note => Self::Cyan,
        }
    }
}

impl Label {
    pub fn new(source: Source, span: Span, ty: LabelType) -> Self {
        Self {
            source,
            span,
            ty,
            message: None,
            order: 0,
            priority: 0,
        }
    }

    /// See [`ariadne::Label::with_message`].
    pub fn with_message(mut self, message: impl ToString) -> Self {
        self.message = Some(message.to_string());
        self
    }

    /// See [`ariadne::Label::with_order`].
    pub fn with_order(mut self, order: i32) -> Self {
        self.order = order;
        self
    }

    /// See [`ariadne::Label::with_priority`].
    pub fn with_priority(mut self, priority: i32) -> Self {
        self.priority = priority;
        self
    }
}

/// Short for "diagnostic result".
///
/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
///
/// If no reports are provided, this does not allocate, and has roughly the same cost as a normal `Result`.
/// If using [`std::sync::Arc`] or similar to encapsulate a value together with reports, the [`Dr`] should
/// typically be the outermost container. This is because we are optimising for the path on which no
/// reports are emitted, so the cost is negligible, and it provides for a nicer API since we have direct
/// access to all of [`Dr`]'s methods.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "errors must be processed by an ErrorEmitter"]
pub struct Dr<T> {
    /// If this is `None`, then the computation failed. Error messages will be contained inside `reports`.
    /// If this is `Some`, then the computation succeeded, but there may still be some messages (e.g. warnings
    /// or errors) inside `messages`.
    value: Option<T>,
    reports: Vec<Report>,
}

impl<T> From<T> for Dr<T> {
    fn from(value: T) -> Self {
        Self::ok(value)
    }
}

impl<T> From<Result<T, Report>> for Dr<T> {
    fn from(result: Result<T, Report>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(error) => Self::fail(error),
        }
    }
}

impl<T> From<Result<T, Vec<Report>>> for Dr<T> {
    fn from(result: Result<T, Vec<Report>>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(errors) => Self::fail_many(errors),
        }
    }
}

impl<T> Dr<T> {
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
        assert!(report.kind == ReportKind::Error);
        Self {
            value: None,
            reports: vec![report],
        }
    }

    pub fn fail_many(reports: Vec<Report>) -> Self {
        assert!(reports.iter().any(|m| m.kind == ReportKind::Error));
        Self {
            value: None,
            reports,
        }
    }

    /// Apply an infallible operation to the value inside this result. If the operation could fail, use [`Dr::bind`] instead.
    pub fn map<F, U>(self, f: F) -> Dr<U>
    where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => Dr {
                value: Some(f(value)),
                reports: self.reports,
            },
            None => Dr {
                value: None,
                reports: self.reports,
            },
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> Dr<U>
    where
        F: FnOnce(T) -> Dr<U>,
    {
        match self.value {
            Some(value) => {
                let mut result = f(value);
                self.reports.append(&mut result.reports);
                Dr {
                    value: result.value,
                    reports: self.reports,
                }
            }
            None => Dr {
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
    pub fn unfail(self) -> Dr<Option<T>> {
        Dr {
            value: Some(self.value),
            reports: self.reports,
        }
    }

    /// Converts a successful diagnostic that had one or more `Error` reports into a failed diagnostic (with the same reports).
    /// Diagnostics without `Error` reports are unaffected.
    pub fn deny(self) -> Self {
        if self.reports.iter().any(|m| m.kind == ReportKind::Error) {
            Self {
                value: None,
                reports: self.reports,
            }
        } else {
            self
        }
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    pub fn sequence(results: impl IntoIterator<Item = Dr<T>>) -> Dr<Vec<T>> {
        results.into_iter().fold(Dr::ok(Vec::new()), |acc, i| {
            acc.bind(|mut list| {
                i.bind(|i| {
                    list.push(i);
                    Dr::ok(list)
                })
            })
        })
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    pub fn sequence_unfail(results: impl IntoIterator<Item = Dr<T>>) -> Dr<Vec<T>> {
        results.into_iter().fold(Dr::ok(Vec::new()), |acc, i| {
            acc.bind(|mut list| {
                i.unfail().bind(|i| {
                    if let Some(i) = i {
                        list.push(i);
                    }
                    Dr::ok(list)
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

    /// Returns true if there was an error report.
    /// If `failed` is true, then `errored` is true.
    pub fn errored(&self) -> bool {
        self.reports
            .iter()
            .any(|report| report.kind == ReportKind::Error)
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

    /// Retrieves the list of reports.
    pub fn reports(&self) -> &[Report] {
        &self.reports
    }

    /// Returns a diagnostic result with the same reports, but where the value is borrowed.
    pub fn as_ref(&self) -> Dr<&T> {
        Dr {
            value: self.value.as_ref(),
            reports: self.reports.clone(),
        }
    }

    /// Returns a diagnostic result with the same reports, but where the value is dereferenced.
    pub fn as_deref(&self) -> Dr<&T::Target>
    where
        T: Deref,
    {
        Dr {
            value: self.value.as_deref(),
            reports: self.reports.clone(),
        }
    }

    /// If there were any errors, panic.
    /// Useful for tests.
    pub fn assert_ok(&self) {
        if self.errored() {
            panic!("diagnostic result contained errors: {:#?}", self.reports);
        }
    }

    /// If there were no errors, return the underlying value.
    /// Useful for tests.
    pub fn unwrap(self) -> T {
        self.assert_ok();
        self.value.unwrap()
    }

    /// If there were no errors, panic.
    /// Useful for tests.
    pub fn assert_errored(&self) {
        if !self.errored() {
            panic!(
                "diagnostic result was supposed to contain errors, reports were: {:#?}",
                self.reports
            );
        }
    }
}

impl<T> FromIterator<Dr<T>> for Dr<Vec<T>> {
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    fn from_iter<U: IntoIterator<Item = Dr<T>>>(iter: U) -> Self {
        Dr::sequence_unfail(iter)
    }
}
