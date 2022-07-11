mod semantic_tokens;

use std::error::Error;
use std::path::Component;
use std::sync::Arc;

use lsp_types::notification::DidOpenTextDocument;
use lsp_types::request::SemanticTokensFullRequest;
use lsp_types::{InitializeParams, ServerCapabilities, Url};
use lsp_types::{
    OneOf, SemanticTokens, SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensResult,
    SemanticTokensServerCapabilities, WorkDoneProgressOptions,
};

use fcommon::{FileReader, Path, PathData};
use fcommon::{Intern, Source, SourceType};
use lsp_server::{Connection, ExtractError, Message, Notification, Request, RequestId, Response};
use qdb::QuillDatabase;
use salsa::Durability;
use tracing::Level;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    tracing_subscriber::fmt()
        .with_ansi(false)
        .with_writer(std::io::stderr)
        .with_max_level(Level::TRACE)
        .init();

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&ServerCapabilities {
        definition_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                work_done_progress_options: WorkDoneProgressOptions {
                    work_done_progress: None,
                },
                legend: crate::semantic_tokens::semantic_tokens_legend(),
                range: None,
                full: Some(SemanticTokensFullOptions::Bool(true)),
            },
        )),
        ..Default::default()
    })
    .unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    main_loop(connection, initialization_params)?;
    io_threads.join()?;

    // Shut down gracefully.
    tracing::debug!("shutting down server");
    Ok(())
}

fn main_loop(
    connection: Connection,
    params: serde_json::Value,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let params: InitializeParams = serde_json::from_value(params).unwrap();
    tracing::debug!("starting example main loop");
    let (mut db, rx) = QuillDatabase::new();
    db.set_project_root_with_durability(
        Arc::new(
            params
                .root_uri.as_ref()
                .expect("language server was not opened in a folder")
                .to_file_path()
                .expect("could not convert URL to file path"),
        ),
        Durability::HIGH,
    );
    for msg in &connection.receiver {
        tracing::debug!("got msg: {:?}", msg);
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
                                Source {
                                    path: relativise(
                                        &db,
                                        params.root_uri.as_ref().unwrap(),
                                        &inner_params.text_document.uri,
                                    ),
                                    ty: SourceType::Quill,
                                },
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
            Message::Notification(not) => {
                tracing::debug!("got notification: {:?}", not);
                match cast_not::<DidOpenTextDocument>(not) {
                    Ok((id, params)) => {
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

fn relativise(db: &QuillDatabase, root_uri: &Url, url: &Url) -> Path {
    let mut path_data = Vec::new();
    for component in url
        .to_file_path()
        .unwrap()
        .strip_prefix(root_uri.to_file_path().unwrap())
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
