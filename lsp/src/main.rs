use std::collections::{BTreeMap, BTreeSet, HashMap};
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

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Name {
  pub name: (String, String),
  pub is_type: bool,
  pub is_foreign: bool,
  pub is_generic: bool,
  pub def_at: Span,
  pub usages: Vec<Span>,
}

fn copy_name<'t>(
  name_resolution::Name {
    name: (a, b),
    is_type,
    is_foreign,
    is_generic,
    def_at,
    usages,
  }: &name_resolution::Name<'t>,
) -> Name {
  Name {
    name: (a.to_string(), b.to_string()),
    is_type: *is_type,
    is_foreign: *is_foreign,
    is_generic: *is_generic,
    def_at: *def_at,
    usages: usages.clone(),
  }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct NameId(usize);
#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct FieldId(usize);

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum CType {
  NodeType(NameId),
  // TODO - add Error type so we can report multiple errors and stuff
  Unknown,
  Foreign(Name),
  // Is this a good idea to code here?
  // Generics do not need to take up node types
  Generic(usize),
  Record(BTreeMap<FieldId, NameId>, bool),
  // TODO: Can the element type be a NameId? Remove Apply and use Function everywhere.
  Apply(Box<CType>, Vec<CType>),
  Function(Box<CType>, Box<CType>),
}

fn copy_type<'t>(ty: &sylt_lib::type_checker::CType<'t>) -> CType {
  use sylt_lib::type_checker::CType as C;
  use CType::*;
  match ty {
    C::NodeType(x) => NodeType(NameId(x.0)),
    C::Unknown => Unknown,
    C::Foreign(name) => Foreign(copy_name(name)),
    C::Generic(g) => Generic(*g),
    C::Record(f, o) => Record(
      f.iter().map(|(a, b)| (FieldId(a.0), NameId(b.0))).collect(),
      *o,
    ),
    C::Apply(a, xs) => Apply(Box::new(copy_type(a)), xs.iter().map(copy_type).collect()),
    C::Function(a, b) => Function(Box::new(copy_type(a)), Box::new(copy_type(b))),
  }
}

#[derive(Clone, Debug)]
pub enum Node {
  Child(NameId),
  Ty(CType),
}

fn copy_node<'t>(node: &sylt_lib::type_checker::Node<'t>) -> Node {
  use Node::*;
  match node {
    type_checker::Node::Child(x) => Child(NameId(x.0)),
    type_checker::Node::Ty(ty) => Ty(copy_type(ty)),
  }
}

#[derive(Debug)]
struct Backend {
  client: Client,
  fid_to_uri_map: DashMap<Fid, (Url, i32)>,
  document_map: DashMap<Fid, Rope>,
  operator_file: RwLock<Option<Rope>>,
  //
  types: RwLock<Vec<Node>>,
  names: RwLock<Vec<Name>>,
  fields: RwLock<Vec<String>>,
}

fn to_id<T: Hash>(t: &Url) -> Fid {
  let mut s = DefaultHasher::new();
  t.hash(&mut s);
  Fid(s.finish().try_into().unwrap())
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
    let mut names_ = self.names.write().unwrap();
    *names_ = names.iter().map(copy_name).collect();
    let mut fields_ = self.fields.write().unwrap();
    // NOTE[et]: BTreeMap has sorted keys, which means we can remove the index for fast random
    // lookups
    *fields_ = fields.iter().map(|(_, b)| b.to_string()).collect();

    // NOTE[et]: types could easily make some nice hover tool tips
    let (types, type_err) = type_checker::check(&names, &named_ast, &fields);
    if let Err(err) = type_err {
      return vec![err];
    }
    let mut types_ = self.types.write().unwrap();
    *types_ = types.iter().map(copy_node).collect();
    Vec::new()
  }

  fn render_type(&self, name: &CType) -> String {
    use CType::*;
    match name {
      NodeType(name_id) => {
        let types = self.types.read().unwrap();
        let mut r = &types[name_id.0];
        while let Node::Child(c) = r {
          r = &types[c.0];
        }
        match r {
          Node::Ty(ty) => self.render_type(&ty),
          _ => unreachable!(),
        }
      }
      Unknown => "_".to_string(),
      Foreign(name) => format!("{}", name.name.1),
      Generic(usize) => format!("t{}", usize),
      Record(fields, open) => {
        let mut out = "".to_string();
        for (i, (fid, ty)) in fields.iter().enumerate() {
          if i != 0 {
            out = format!("{}, ", out);
          }
          out = format!(
            "{} {}: {}",
            out,
            self.fields.read().unwrap().get(fid.0).unwrap(),
            self.render_type(&NodeType(*ty))
          );
        }
        format!("{{ {} {} }}", out, if *open { " | _ " } else { "" })
      }
      Apply(a, bs) => {
        let a = self.render_type(a);
        let bs = bs
          .iter()
          .map(|b| self.render_type(b))
          .collect::<Vec<_>>()
          .join(" ");
        format!("{} {}", a, bs)
      }
      Function(a, b) => {
        let a = self.render_type(a);
        let b = self.render_type(b);
        format!("{} -> {}", a, b)
      }
    }
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
    names: RwLock::new(Vec::new()),
    types: RwLock::new(Vec::new()),
    fields: RwLock::new(Vec::new()),
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

fn position_to_span(p: Position, fid: Fid, ropes: &DashMap<Fid, Rope>) -> Option<Span> {
  let rope = ropes.get(&fid)?;
  let offset = position_to_offset(p, &rope);
  Some(sylt_lib::error::Span(offset, offset, fid.0))
}

fn position_to_offset(Position { line, character }: Position, rope: &Rope) -> usize {
  let o: usize = character.try_into().unwrap();
  rope.line_to_char(line.try_into().unwrap()) + o
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
        references_provider: Some(OneOf::Left(true)),
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
    let uri = params.text_document_position_params.text_document.uri;
    let fid = to_id::<Url>(&uri);
    self
      .client
      .log_message(
        MessageType::ERROR,
        format!(
          "Failed to convert span {:?}",
          params.text_document_position_params.position
        ),
      )
      .await;
    let at = if let Some(at) = position_to_span(
      params.text_document_position_params.position,
      fid,
      &self.document_map,
    ) {
      at
    } else {
      return Ok(None);
    };
    self
      .client
      .log_message(MessageType::ERROR, format!("No overlap {:?}", at))
      .await;
    let (i, m) = if let Some(m) = self
      .names
      .read()
      .unwrap()
      .iter()
      .enumerate()
      .find(|(_, name)| name.def_at.overlaps(at) || name.usages.iter().any(|s| s.overlaps(at)))
      .map(|(a, b)| (a, b.clone()))
    {
      m
    } else {
      return Ok(None);
    };
    let x = self.render_type(&CType::NodeType(NameId(i)));

    Ok(Some(Hover {
      range: None,
      contents: HoverContents::Markup(MarkupContent {
        kind: MarkupKind::Markdown,
        value: format!("{}.{} : {} \n<{}>", m.name.0, m.name.1, x, m.usages.len()),
      }),
    }))
  }

  async fn goto_definition(
    &self,
    params: GotoDefinitionParams,
  ) -> Result<Option<GotoDefinitionResponse>> {
    let uri = params.text_document_position_params.text_document.uri;
    let fid = to_id::<Url>(&uri);
    let at = if let Some(at) = position_to_span(
      params.text_document_position_params.position,
      fid,
      &self.document_map,
    ) {
      at
    } else {
      return Ok(None);
    };
    let (_, m) = if let Some(m) = self
      .names
      .read()
      .unwrap()
      .iter()
      .enumerate()
      .find(|(_, name)| name.def_at.overlaps(at) || name.usages.iter().any(|s| s.overlaps(at)))
      .map(|(a, b)| (a, b.clone()))
    {
      m
    } else {
      return Ok(None);
    };

    let (at, range) = span_to_range(m.def_at, &self.document_map).unwrap();
    let uri = self.fid_to_uri_map.get(&at).unwrap();
    Ok(Some(GotoDefinitionResponse::Scalar(Location::new(
      uri.0.clone(),
      range,
    ))))
  }

  async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
    let include_definition = params.context.include_declaration;
    let uri = params.text_document_position.text_document.uri;
    let fid = to_id::<Url>(&uri);
    let at = if let Some(at) = position_to_span(
      params.text_document_position.position,
      fid,
      &self.document_map,
    ) {
      at
    } else {
      return Ok(None);
    };
    let (_, m) = if let Some(m) = self
      .names
      .read()
      .unwrap()
      .iter()
      .enumerate()
      .find(|(_, name)| name.def_at.overlaps(at) || name.usages.iter().any(|s| s.overlaps(at)))
      .map(|(a, b)| (a, b.clone()))
    {
      m
    } else {
      return Ok(None);
    };

    Ok(Some(
      m.usages
        .iter()
        .cloned()
        .chain(vec![m.def_at])
        .collect::<BTreeSet<_>>()
        .iter()
        .filter(|s| **s != m.def_at || include_definition)
        .map(|s| {
          let (at, range) = span_to_range(*s, &self.document_map).unwrap();
          let uri = self.fid_to_uri_map.get(&at).unwrap();
          Location::new(uri.0.clone(), range)
        })
        .collect(),
    ))
  }
}
