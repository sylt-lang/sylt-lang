use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::RwLock;

use dashmap::DashMap;
use ropey::Rope;
use serde_json::Value;
use sylt_lib::error::{Error, Span};
use sylt_lib::{name_resolution, type_checker, PREAMBLE};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd, Hash)]
struct Fid(usize);

#[derive(Debug)]
struct Backend {
  client: Client,
  fid_to_uri_map: DashMap<Fid, (Url, i32)>,
  document_map: DashMap<Fid, Rope>,
  operator_file: RwLock<Option<Rope>>,
  // semantic_token_map: DashMap<String, Vec<ImCompleteSemanticToken>>,
}

fn to_id<T: Hash>(t: &Url) -> Fid {
  let mut s = DefaultHasher::new();
  t.hash(&mut s);
  Fid(s.finish().try_into().unwrap())
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
  async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
    Ok(InitializeResult {
      server_info: None, // Some(ServerInfo { name: "sylt-lsp".to_string(), version: None }),
      offset_encoding: None,
      capabilities: ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        definition_provider: Some(OneOf::Left(true)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
          identifier: None,
          inter_file_dependencies: true,
          workspace_diagnostics: false,
          work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None },
        })),
        ..ServerCapabilities::default()
      },
    })
  }
  async fn initialized(&self, _: InitializedParams) {
    self
      .client
      .log_message(MessageType::ERROR, "initialized!")
      .await;
  }

  async fn shutdown(&self) -> Result<()> {
    Ok(())
  }

  async fn did_open(&self, params: DidOpenTextDocumentParams) {
    self
      .client
      .log_message(MessageType::ERROR, "file opened!")
      .await;
    self
      .on_change(TextDocumentItem {
        uri: params.text_document.uri,
        text: params.text_document.text,
        version: params.text_document.version,
      })
      .await
  }

  async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
    self
      .on_change(TextDocumentItem {
        uri: params.text_document.uri,
        text: std::mem::take(&mut params.content_changes[0].text),
        version: params.text_document.version,
      })
      .await
  }

  async fn did_save(&self, _: DidSaveTextDocumentParams) {
    self
      .client
      .log_message(MessageType::ERROR, "file saved!")
      .await;
  }
  async fn did_close(&self, _: DidCloseTextDocumentParams) {
    self
      .client
      .log_message(MessageType::ERROR, "file closed!")
      .await;
  }

  async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
    self
      .client
      .log_message(MessageType::ERROR, "configuration changed!")
      .await;
  }

  async fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {
    self
      .client
      .log_message(MessageType::ERROR, "workspace folders changed!")
      .await;
  }

  async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
    self
      .client
      .log_message(MessageType::ERROR, "watched files have changed!")
      .await;
  }

  async fn execute_command(&self, _: ExecuteCommandParams) -> Result<Option<Value>> {
    self
      .client
      .log_message(MessageType::ERROR, "command executed!")
      .await;

    match self.client.apply_edit(WorkspaceEdit::default()).await {
      Ok(res) if res.applied => self.client.log_message(MessageType::ERROR, "applied").await,
      Ok(_) => {
        self
          .client
          .log_message(MessageType::ERROR, "rejected")
          .await
      }
      Err(err) => self.client.log_message(MessageType::ERROR, err).await,
    }

    Ok(None)
  }

  async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
    let _ = params;
    Ok(Some(Hover {
      range: None,
      contents: HoverContents::Markup(MarkupContent {
        kind: MarkupKind::Markdown,
        value: "# ABCD".to_string(),
      }),
    }))
  }
}

struct TextDocumentItem {
  uri: Url,
  text: String,
  version: i32,
}

impl Backend {
  fn id_to_uri(&self, x: &Fid) -> Option<(Url, i32)> {
    self.fid_to_uri_map.get(x).map(|y| y.clone())
  }

  fn add_uri(&self, u: Url, v: i32) -> Fid {
    let i = to_id::<Url>(&u);
    self.fid_to_uri_map.insert(i, (u, v));
    i
  }

  async fn on_change(&self, params: TextDocumentItem) {
    self
      .client
      .log_message(MessageType::ERROR, format!("on_change: {}", params.uri))
      .await;
    let rope = ropey::Rope::from_str(&params.text);

    if params.uri.to_string().ends_with(".syop") {
      match sylt_lib::hexer::parse(&params.text) {
        Ok(ops) => {
          // ROPE is useless here
          *self.operator_file.write().unwrap() = Some(rope.clone());
          self
            .client
            .log_message(
              MessageType::ERROR,
              format!("successful operator parse: {} {:?}", params.uri, ops),
            )
            .await;
          self
            .client
            .publish_diagnostics(params.uri, vec![], Some(params.version))
            .await;
          return;
        }
        Err(err) => {
          let (msg, _) = err.convert();
          self
            .client
            .log_message(
              MessageType::ERROR,
              format!("error operator parse: {}", params.uri),
            )
            .await;
          self
            .client
            .publish_diagnostics(
              params.uri,
              vec![Diagnostic::new_simple(
                Range::new(Position::new(0, 0), Position::new(0, 0)),
                msg,
              )],
              Some(params.version),
            )
            .await;
          return;
        }
      }
    }

    let ops_source = self
      .operator_file
      .read()
      .unwrap()
      .as_ref()
      .map(|x| x.to_string())
      .unwrap_or_else(|| sylt_lib::OPERATORS.to_string());
    let ops = sylt_lib::hexer::parse(&ops_source).unwrap();
    // TODO: Handle operators file
    let id = self.add_uri(params.uri.clone(), params.version);
    self.document_map.insert(id, rope.clone());
    let mut diagnostics = match sylt_lib::parser::parse(&params.text, id.0, ops) {
      Ok(_ast) => Vec::new(),
      Err(errs) => errs
        .into_iter()
        .filter_map(|err| {
          let (msg, annots) = err.convert();
          let span = annots.last().cloned().unwrap_or(Span(0, 0, id.0));
          let (file, range) = span_to_range(span, &self.document_map)?;
          Some((file, Diagnostic::new_simple(range, msg)))
        })
        .collect(),
    };
    if diagnostics.is_empty() {
      self
        .client
        .publish_diagnostics(params.uri, vec![], Some(params.version))
        .await;
      diagnostics = self
        .try_to_recompile_everything()
        .await
        .into_iter()
        .filter_map(|err| {
          let (msg, annots) = err.convert();
          let span = annots.last().cloned().unwrap_or(Span(0, 0, id.0));
          let (file, range) = span_to_range(span, &self.document_map)?;
          Some((file, Diagnostic::new_simple(range, msg)))
        })
        .collect();
    }

    let mut msg = HashMap::new();
    for (i, d) in diagnostics.into_iter() {
      msg.entry(i).or_insert(Vec::new()).push(d);
    }
    for (i, d) in msg.into_iter() {
      self
        .client
        .log_message(MessageType::ERROR, "send_diagnostic")
        .await;
      let (url, version) = self.id_to_uri(&i).unwrap().clone();
      self.client.publish_diagnostics(url, d, Some(version)).await;
    }
  }

  async fn try_to_recompile_everything(&self) -> Vec<Error> {
    let ops_source = self
      .operator_file
      .read()
      .unwrap()
      .as_ref()
      .map(|x| x.to_string())
      .unwrap_or_else(|| sylt_lib::OPERATORS.to_string());
    let ops = sylt_lib::hexer::parse(&ops_source).unwrap();
    // TODO: operators
    // I probably don't want an `alter_all` here - I guess `shards` is the right call but I'm not
    // gonna dig into that at the moment.
    // I think this also tells me the entire approach is wrong - either I store intermediate
    // results here or I need a different structure to handle all this data. Then again, this
    // shouldn't be too heavy to copy at most a couple megabytes TBH.
    let mut source = Vec::new();
    self.document_map.alter_all(|k, s| {
      source.push((*k, s.to_string()));
      s
    });
    source.push((Fid(0), PREAMBLE.to_string()));

    let mut errors = Vec::new();
    let asts = source
      .iter()
      .filter_map(
        |(fid, source)| match sylt_lib::parser::parse(source, fid.0, ops.clone()) {
          Ok(ast) => Some(ast),
          Err(errs) => {
            for e in errs.into_iter() {
              errors.push(e);
            }
            None
          }
        },
      )
      .collect::<Vec<_>>();
    if !errors.is_empty() {
      return errors;
    }

    let combined_ast: Vec<_> = asts
      .into_iter()
      .filter_map(|x| Some(x))
      .map(|(m, xs)| xs.into_iter().map(|x| (m, x)).collect::<Vec<_>>())
      .flatten()
      .collect::<Vec<_>>();

    let (names, fields, named_ast) = match name_resolution::resolve(combined_ast) {
      Err(errs) => {
        return errs;
      }
      Ok(a) => a,
    };

    // NOTE[et]: types could easily make some nice hover tool tips
    let (_types, type_err) = type_checker::check(&names, &named_ast, &fields);
    if let Err(err) = type_err {
      return vec![err];
    }
    Vec::new()
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
    fid_to_uri_map: DashMap::new(),
    operator_file: RwLock::new(None),
  })
  .finish();

  Server::new(stdin, stdout, socket).serve(service).await;
}

fn span_to_range(
  sylt_lib::error::Span(lo, hi, file): sylt_lib::error::Span,
  ropes: &DashMap<Fid, Rope>,
) -> Option<(Fid, Range)> {
  let rope = &ropes.get(&Fid(file))?;
  let lo = offset_to_position(lo, rope)?;
  let hi = offset_to_position(hi, rope)?;
  Some((Fid(file), Range::new(lo, hi)))
}

fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
  let line = rope.try_char_to_line(offset).ok()?;
  let first_char_of_line = rope.try_line_to_char(line).ok()?;
  let column = offset - first_char_of_line;
  Some(Position::new(line as u32, column as u32))
}
