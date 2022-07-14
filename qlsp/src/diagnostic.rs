use fcommon::{Report, ReportKind};
use lsp_types::{Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, Url};
use qdb::QuillDatabase;

use crate::range::MultiRangeData;

pub fn into_diagnostics(
    db: &QuillDatabase,
    uri: &Url,
    reports: impl IntoIterator<Item = Report>,
) -> Vec<Diagnostic> {
    let mut range_data = MultiRangeData::new(db);
    reports
        .into_iter()
        .map(|report| into_diagnostic(&mut range_data, uri, report))
        .collect()
}

fn into_diagnostic(range_data: &mut MultiRangeData, uri: &Url, report: Report) -> Diagnostic {
    Diagnostic {
        range: range_data.range_data(report.source).span_to_range(
            report
                .labels
                .get(0)
                .unwrap_or_else(|| {
                    panic!(
                        "diagnostic with message {:?} did not have any labels",
                        report.message
                    )
                })
                .span
                .clone(),
        ),
        severity: Some(match report.kind {
            ReportKind::Error => DiagnosticSeverity::ERROR,
            ReportKind::Warning => DiagnosticSeverity::WARNING,
        }),
        code: None,
        code_description: None,
        source: Some("quill_lsp".to_string()),
        message: report
            .message
            .unwrap_or_else(|| "(no error message)".to_owned()),
        related_information: Some(
            report
                .labels
                .iter()
                .map(|label| DiagnosticRelatedInformation {
                    location: Location {
                        uri: uri.clone(),
                        range: range_data
                            .range_data(label.source)
                            .span_to_range(label.span.clone()),
                    },
                    message: label
                        .message
                        .as_deref()
                        .unwrap_or("(no message)")
                        .to_owned(),
                })
                .collect(),
        ),
        tags: None,
        data: None,
    }
}
