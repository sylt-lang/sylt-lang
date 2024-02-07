use dashmap::DashMap;
use ropey::Rope;
use serde_json::Value;
use sylt_lib::error::Error;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
#[derive(Debug)]
struct Backend {
    client: Client,
    // ast_map: DashMap<String, HashMap<String, Func>>,
    document_map: DashMap<String, Rope>,
    // semantic_token_map: DashMap<String, Vec<ImCompleteSemanticToken>>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            server_info: None, // Some(ServerInfo { name: "sylt-lsp".to_string(), version: None }),
            offset_encoding: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                definition_provider: Some(OneOf::Left(true)),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                diagnostic_provider: Some(
                    DiagnosticServerCapabilities::Options(DiagnosticOptions {
                            identifier: None,
                            inter_file_dependencies: true, workspace_diagnostics: false, work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None } })),
                ..ServerCapabilities::default()
            },
        })
    }
    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "initialized!")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file opened!")
            .await;
        self.on_change(TextDocumentItem {
            uri: params.text_document.uri,
            text: params.text_document.text,
            version: params.text_document.version,
        })
        .await
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        self.on_change(TextDocumentItem {
            uri: params.text_document.uri,
            text: std::mem::take(&mut params.content_changes[0].text),
            version: params.text_document.version,
        })
        .await
    }

    async fn did_save(&self, _: DidSaveTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file saved!")
            .await;
    }
    async fn did_close(&self, _: DidCloseTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file closed!")
            .await;
    }

    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        self.client
            .log_message(MessageType::INFO, "configuration changed!")
            .await;
    }

    async fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {
        self.client
            .log_message(MessageType::INFO, "workspace folders changed!")
            .await;
    }

    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        self.client
            .log_message(MessageType::INFO, "watched files have changed!")
            .await;
    }

    async fn execute_command(&self, _: ExecuteCommandParams) -> Result<Option<Value>> {
        self.client
            .log_message(MessageType::INFO, "command executed!")
            .await;

        match self.client.apply_edit(WorkspaceEdit::default()).await {
            Ok(res) if res.applied => self.client.log_message(MessageType::INFO, "applied").await,
            Ok(_) => self.client.log_message(MessageType::INFO, "rejected").await,
            Err(err) => self.client.log_message(MessageType::ERROR, err).await,
        }

        Ok(None)
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let _ = params;
        Ok(Some(Hover { range: None, contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown
                , 
            value: "# ABC".to_string(),
        }) }))
    }
}

struct TextDocumentItem {
    uri: Url,
    text: String,
    version: i32,
}

impl Backend {
    async fn on_change(&self, params: TextDocumentItem) {
        let rope = ropey::Rope::from_str(&params.text);
        self.document_map
            .insert(params.uri.to_string(), rope.clone());
        let ops = sylt_lib::hexer::parse(sylt_lib::OPERATORS).unwrap();
        let diagnostics = match sylt_lib::parser::parse(&params.text, 0, ops) {
            Ok(_ast) => Vec::new(),
            Err(errs) => {
                errs.into_iter().filter_map(|err|
                    match err {
                        Error::Special(msg) => {
                            Some(Diagnostic::new_simple(Range::new(Position::new(0, 0), Position::new(0, 0)), msg))
                        }
                        Error::SynMsg { msg, span, token: Some(token) } => {
                            Some(Diagnostic::new_simple(span_to_range(span, &rope)?, format!("{} - expected {}", msg.to_string(), token)))
                        }
                        Error::SynMsg { msg, span, token: None } => {
                            Some(Diagnostic::new_simple(span_to_range(span, &rope)?, format!("{}", msg.to_string())))
                        }
                        Error::SynEoF { span } => {
                            Some(Diagnostic::new_simple(span_to_range(span, &rope)?, format!("Unexpected end of file")))
                        }
                        _ => None,
                        // Error::ResUnknown { ns, name, span } => todo!(),
                        // Error::ResMultiple { ns, name, original, new } => todo!(),
                        // Error::ResNoEnumConst { ty_name, at, const_name } => todo!(),
                        // Error::ResNoEnum { ty_name, at } => todo!(),
                        // Error::ResMsg { msg, span } => todo!(),
                        // Error::CheckMsg { msg, a_span, b_span } => todo!(),
                        // Error::CheckExpected { msg, span, a } => todo!(),
                        // Error::CheckReq { msg, span, a, req } => todo!(),
                        // Error::CheckUnify { msg, a, b, span } => todo!(),
                        // Error::CheckExtraLabel { a, b, field, span } => todo!(),
                        // Error::CheckField { field, inner } => todo!(),
                    }
                ).collect()
            }
        };
//         let ParserResult {
//             ast,
//             parse_errors,
//             semantic_tokens,
//         } = parse(&params.text);
//         let diagnostics = parse_errors
//             .into_iter()
//             .filter_map(|item| {
//                 let (message, span) = match item.reason() {
//                     chumsky::error::SimpleReason::Unclosed { span, delimiter } => {
//                         (format!("Unclosed delimiter {}", delimiter), span.clone())
//                     }
//                     chumsky::error::SimpleReason::Unexpected => (
//                         format!(
//                             "{}, expected {}",
//                             if item.found().is_some() {
//                                 "Unexpected token in input"
//                             } else {
//                                 "Unexpected end of input"
//                             },
//                             if item.expected().len() == 0 {
//                                 "something else".to_string()
//                             } else {
//                                 item.expected()
//                                     .map(|expected| match expected {
//                                         Some(expected) => expected.to_string(),
//                                         None => "end of input".to_string(),
//                                     })
//                                     .collect::<Vec<_>>()
//                                     .join(", ")
//                             }
//                         ),
//                         item.span(),
//                     ),
//                     chumsky::error::SimpleReason::Custom(msg) => (msg.to_string(), item.span()),
//                 };
// 
//                 || -> Option<Diagnostic> {
//                     let start_position = offset_to_position(span.start, &rope)?;
//                     let end_position = offset_to_position(span.end, &rope)?;
//                     Some(Diagnostic::new_simple(
//                         Range::new(start_position, end_position),
//                         message,
//                     ))
//                 }()
//             })
//             .collect::<Vec<_>>();
        self.client
            .publish_diagnostics(params.uri.clone(), diagnostics, Some(params.version))
            .await;

        // if let Some(ast) = ast {
        //     self.ast_map.insert(params.uri.to_string(), ast);
        // }
        // self.client
        //     .log_message(MessageType::INFO, &format!("{:?}", semantic_tokens))
        //     .await;
        // self.semantic_token_map
        //     .insert(params.uri.to_string(), semantic_tokens);
    }
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(|client| Backend {
        client,
        document_map: DashMap::new(),
    })
    .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}

fn span_to_range(sylt_lib::error::Span(lo, hi, _file): sylt_lib::error::Span, rope: &Rope) -> Option<Range> {
    let lo = offset_to_position(lo, rope)?;
    let hi = offset_to_position(hi, rope)?;
    Some(Range::new(lo, hi))
}

fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_char_to_line(offset).ok()?;
    let first_char_of_line = rope.try_line_to_char(line).ok()?;
    let column = offset - first_char_of_line;
    Some(Position::new(line as u32, column as u32))
}
