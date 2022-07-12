mod semantic_tokens;

use std::error::Error;
use std::fmt::Debug;
use std::path::Component;
use std::str::FromStr;
use std::sync::Arc;

use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument};
use lsp_types::request::SemanticTokensFullRequest;
use lsp_types::{
    InitializeParams, ServerCapabilities, TextDocumentItem, TextDocumentSyncCapability,
    TextDocumentSyncKind, Url,
};
use lsp_types::{
    OneOf, SemanticTokens, SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensResult,
    SemanticTokensServerCapabilities, WorkDoneProgressOptions,
};

use fcommon::{FileReader, Path, PathData};
use fcommon::{Intern, Source, SourceType};
use qdb::QuillDatabase;
use salsa::{Durability, ParallelDatabase, Snapshot};
use tokio::sync::mpsc::Sender;
use tokio::sync::RwLock;
use tracing::Level;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

struct Backend {
    client: Client,
    tx: Sender<Box<dyn Send + Sync + FnOnce(&mut QuillDatabase)>>,
    root_uri: RwLock<Url>,
}

impl Debug for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<backend>")
    }
}

impl Backend {
    async fn with_db(&self, f: Box<dyn Send + Sync + FnOnce(&mut QuillDatabase)>) {
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

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let root_uri = self.root_uri.read().await.clone();
        self.with_db(Box::new(move |db| {
            let source = source_from_text_document(db, &root_uri, &params.text_document.uri);
            db.overwritten_files().write().unwrap().overwrite_file(
                db,
                source,
                params.text_document.text,
            );
        }))
        .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Since we only support `TextDocumentSyncKind::FULL`, there must only be one content change,
        // and this is the entire contents of the file.
        let root_uri = self.root_uri.read().await.clone();
        self.with_db(Box::new(move |db| {
            let source = source_from_text_document(db, &root_uri, &params.text_document.uri);
            db.overwritten_files().write().unwrap().overwrite_file(
                db,
                source,
                params.content_changes[0].text.clone(),
            );
        }))
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
                source_from_text_document(&db, &root_uri, &params.text_document.uri),
            ),
        })))
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
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
    let (tx, mut rx) =
        tokio::sync::mpsc::channel::<Box<dyn Send + Sync + FnOnce(&mut QuillDatabase)>>(16);

    tokio::task::spawn_blocking(move || {
        let (mut db, file_rx) = QuillDatabase::new();
        while let Some(value) = rx.blocking_recv() {
            value(&mut db);
        }
    });

    // db.set_project_root_with_durability(
    //     Arc::new(
    //         params
    //             .root_uri
    //             .as_ref()
    //             .expect("language server was not opened in a folder")
    //             .to_file_path()
    //             .expect("could not convert URL to file path"),
    //     ),
    //     Durability::HIGH,
    // );

    let (service, socket) = LspService::new(|client| Backend {
        client,
        tx,
        root_uri: RwLock::new(Url::from_str("about:blank").unwrap()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;

    // Shut down gracefully.
    tracing::debug!("shutting down server");
}

/*
fn main_loop(
    connection: Connection,
    params: serde_json::Value,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let params: InitializeParams = serde_json::from_value(params).unwrap();
    tracing::debug!("starting example main loop");

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                tracing::debug!("got request: {:?}", req);
                match cast::<SemanticTokensFullRequest>(req) {
                    Ok((id, inner_params)) => {
                        let result = Some(SemanticTokensResult::Tokens(SemanticTokens {
                            result_id: None,
                            data: semantic_tokens::create_semantic_tokens(
                                &db,
                                source_from_text_document(
                                    &db,
                                    &params,
                                    &inner_params.text_document.uri,
                                ),
                            ),
                        }));
                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{:?}", err),
                    Err(ExtractError::MethodMismatch(req)) => req,
                };
                // ...
            }
            Message::Response(resp) => {
                tracing::debug!("got response: {:?}", resp);
            }
            Message::Notification(mut not) => {
                tracing::debug!("got notification: {:?}", not);
                not = match cast_not::<DidOpenTextDocument>(not) {
                    Ok((_id, inner_params)) => {
                        let source = source_from_text_document(
                            &db,
                            &params,
                            &inner_params.text_document.uri,
                        );
                        db.overwritten_files().write().unwrap().overwrite_file(
                            &mut db,
                            source,
                            inner_params.text_document.text,
                        );
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{:?}", err),
                    Err(ExtractError::MethodMismatch(not)) => not,
                };
                match cast_not::<DidChangeTextDocument>(not) {
                    Ok((_id, inner_params)) => {
                        // Since we only support `TextDocumentSyncKind::FULL`, there must only be one content change,
                        // and this is the entire contents of the file.
                        let source = source_from_text_document(
                            &db,
                            &params,
                            &inner_params.text_document.uri,
                        );
                        db.overwritten_files().write().unwrap().overwrite_file(
                            &mut db,
                            source,
                            inner_params.content_changes[0].text.clone(),
                        );
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{:?}", err),
                    Err(ExtractError::MethodMismatch(not)) => not,
                };
                // ...
            }
        }
    }
    Ok(())
}

fn cast<R>(req: Request) -> Result<(RequestId, R::Params), ExtractError<Request>>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

fn cast_not<R>(not: Notification) -> Result<(RequestId, R::Params), ExtractError<Notification>>
where
    R: lsp_types::notification::Notification,
    R::Params: serde::de::DeserializeOwned,
{
    not.extract(R::METHOD)
}
 */

fn source_from_text_document(db: &QuillDatabase, root_uri: &Url, uri: &Url) -> Source {
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
