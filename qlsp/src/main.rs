mod diagnostic;
mod range;
mod semantic_tokens;

use std::fmt::Debug;
use std::path::Component;
use std::str::FromStr;
use std::sync::Arc;

use diagnostic::into_diagnostics;
use lsp_types::{
    InitializeParams, ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind, Url,
};
use lsp_types::{
    SemanticTokens, SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensResult,
    SemanticTokensServerCapabilities, WorkDoneProgressOptions,
};

use fcommon::{Dr, FileReader, Path, PathData};
use fcommon::{Intern, Source, SourceType};
use qdb::QuillDatabase;
use qelab::Elaborator;
use salsa::{Durability, ParallelDatabase, Snapshot};
use tokio::sync::mpsc::Sender;
use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use tracing::Level;

/// An operation we can perform on a database.
/// Since the database is not `Send` or `Sync`, the only way to control it through threads is
/// by sending requests to the thread that holds the database. This is that type of request.
type DatabaseOperation = Box<dyn Send + Sync + FnOnce(&mut QuillDatabase)>;

struct Backend {
    client: Client,
    /// Sending things through this channel will put them in a queue to be performed by the
    /// database managing thread.
    tx: Sender<DatabaseOperation>,
    /// Should be set to the root URI of the workspace.
    root_uri: RwLock<Url>,
}

impl Debug for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<backend>")
    }
}

impl Backend {
    async fn with_db(&self, f: DatabaseOperation) {
        let request = self.tx.send(f);
        if request.await.is_err() {
            panic!("could not send database request");
        }
    }

    async fn db(&self) -> Snapshot<QuillDatabase> {
        let (tx, rx) = tokio::sync::oneshot::channel();
        self.with_db(Box::new(|db| {
            tx.send(db.snapshot()).unwrap();
        }))
        .await;
        rx.await.unwrap()
    }

    async fn change_file_contents(&self, uri: Url, contents: String) {
        let (tx, rx) = tokio::sync::oneshot::channel();
        let uri2 = uri.clone();
        let root_uri = self.root_uri.read().await.clone();
        self.with_db(Box::new(move |db| {
            let source = source_from_uri(db, &root_uri, &uri2);
            db.overwritten_files()
                .write()
                .unwrap()
                .overwrite_file(db, source, contents);
            tx.send((source, db.snapshot())).unwrap();
        }))
        .await;
        let client = self.client.clone();
        tokio::spawn(async move {
            let (source, db) = rx.await.unwrap();
            let db2 = db.snapshot();
            let dr: Dr<_> = tokio::task::spawn_blocking(move || {
                db2.source(source)
                    .bind(|file_contents| db2.elaborate_and_certify(source, file_contents))
            })
            .await
            .unwrap();

            let (_, reports) = dr.destructure();
            let diagnostics = into_diagnostics(&db, &uri, reports);
            // This is a slight simplification - not all diagnostics come a priori from this file,
            // but for now let's just publish them all to this file.
            client.publish_diagnostics(uri, diagnostics, None).await;
        });
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, init_params: InitializeParams) -> Result<InitializeResult> {
        let root_uri = init_params
            .root_uri
            .as_ref()
            .expect("language server was not opened in a folder")
            .clone();
        *self.root_uri.write().await = root_uri.clone();
        self.with_db(Box::new(move |db| {
            db.set_project_root_with_durability(
                Arc::new(
                    root_uri
                        .to_file_path()
                        .expect("could not convert URL to file path"),
                ),
                Durability::HIGH,
            );
        }))
        .await;

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            work_done_progress_options: WorkDoneProgressOptions {
                                work_done_progress: None,
                            },
                            legend: crate::semantic_tokens::semantic_tokens_legend(),
                            range: None,
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                        },
                    ),
                ),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "Quill Language Server".to_string(),
                version: None,
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        tracing::info!("server initialised")
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.change_file_contents(params.text_document.uri, params.text_document.text)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Since we only support `TextDocumentSyncKind::FULL`, there must only be one content change,
        // and this is the entire contents of the file.
        self.change_file_contents(
            params.text_document.uri,
            params.content_changes[0].text.clone(),
        )
        .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let root_uri = self.root_uri.read().await;
        let db = self.db().await;
        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: semantic_tokens::create_semantic_tokens(
                &db,
                source_from_uri(&db, &root_uri, &params.text_document.uri),
            ),
        })))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    tracing_subscriber::fmt()
        .with_ansi(false)
        .with_writer(std::io::stderr)
        .with_max_level(Level::TRACE)
        .init();

    // Create a channel to talk to the Quill database.
    // This is required because the database can't move between threads as it uses RefCells.
    let (tx, mut rx) = tokio::sync::mpsc::channel::<DatabaseOperation>(16);

    tokio::task::spawn_blocking(move || {
        // The main loop for the database thread.
        // This thread accepts operations to be performed on the underlying `salsa` database.
        let (mut db, file_rx) = QuillDatabase::new();
        while let Some(value) = rx.blocking_recv() {
            value(&mut db);
        }
    });

    let (service, socket) = LspService::new(|client| Backend {
        client,
        tx,
        root_uri: RwLock::new(Url::from_str("about:blank").unwrap()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;

    // Shut down gracefully.
    tracing::debug!("shutting down server");
}

fn source_from_uri(db: &QuillDatabase, root_uri: &Url, uri: &Url) -> Source {
    Source {
        path: relativise(db, root_uri, uri),
        ty: SourceType::Quill,
    }
}

fn relativise(db: &QuillDatabase, root_uri: &Url, uri: &Url) -> Path {
    let mut path_data = Vec::new();
    for component in uri
        .to_file_path()
        .unwrap()
        .strip_prefix(
            root_uri
                .to_file_path()
                .unwrap_or_else(|()| panic!("{} was not a file path", root_uri)),
        )
        .unwrap()
        .with_extension("")
        .components()
    {
        match component {
            Component::Prefix(_) => todo!(),
            Component::RootDir => todo!(),
            Component::CurDir => todo!(),
            Component::ParentDir => todo!(),
            Component::Normal(segment) => {
                path_data.push(db.intern_string_data(segment.to_string_lossy().to_string()));
            }
        }
    }
    db.intern_path_data(PathData(path_data))
}
