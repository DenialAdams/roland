#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::unwrap_or_default)] // I want to know exactly what is being called

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::DerefMut;
use std::path::PathBuf;

use goto_definition::find_definition;
use parking_lot::{Mutex, RwLock};
use rolandc::error_handling::{ErrorInfo, ErrorLocation, ExpandedErrorLocation, convert_positions_to_line_column};
use rolandc::source_info::{SourceInfo, SourcePath, SourcePosition};
use rolandc::*;
use tower_lsp_server::jsonrpc::{Error, ErrorCode, Result};
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

mod goto_definition;

enum WorkspaceMode {
   LooseFiles,
   EntryPointAndTarget(PathBuf, Target),
   StdLib,
}

struct LSPFileResolver<'a> {
   file_map: &'a HashMap<PathBuf, (String, i32)>,
   touched_paths: &'a mut Vec<PathBuf>,
}

impl FileResolver for LSPFileResolver<'_> {
   const REQUIRES_CANONIZATION: bool = true;
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<Cow<'static, str>> {
      debug_assert_eq!(path, std::fs::canonicalize(path)?);
      let resolved = if let Some(buf) = self.file_map.get(path) {
         Ok(Cow::Owned(buf.0.clone()))
      } else {
         match std::fs::read_to_string(path) {
            Ok(s) => Ok(Cow::Owned(s)),
            Err(e) => Err(e),
         }
      };
      self.touched_paths.push(path.to_path_buf());
      resolved
   }
}

struct Backend {
   client: Client,
   mode: RwLock<WorkspaceMode>,
   opened_files: RwLock<HashMap<PathBuf, (String, i32)>>,
   ctx: Mutex<CompilationContext>,
}

fn roland_source_path_to_canon_path(source_path: &SourcePath, file_map: &FileMap) -> Option<std::io::Result<PathBuf>> {
   let ((path, is_std), _file_contents) = file_map.get_index(source_path.0).unwrap();
   if *is_std {
      // Hit when rolandc provides a reference to a standard library defined type
      return None;
   }
   Some(std::fs::canonicalize(path))
}

fn roland_error_to_lsp_error(
   re: ErrorInfo,
   file_map: &FileMap,
   err_locations: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
   severity: DiagnosticSeverity,
) -> (Option<PathBuf>, Diagnostic) {
   let (report_path, range, mut related_info) = match re.location {
      ErrorLocation::Simple(x) => {
         let (begin_line, begin_col) = err_locations[&(x.file, x.begin.0)];
         let (end_line, end_col) = err_locations[&(x.file, x.end.0)];
         (
            roland_source_path_to_canon_path(&x.file, file_map).map(|x| x.unwrap()),
            Range {
               start: Position {
                  line: begin_line as u32,
                  character: begin_col as u32,
               },
               end: Position {
                  line: end_line as u32,
                  character: end_col as u32,
               },
            },
            Vec::new(),
         )
      }
      ErrorLocation::WithDetails(x) => {
         let (begin_line, begin_col) = err_locations[&(x[0].0.file, x[0].0.begin.0)];
         let (end_line, end_col) = err_locations[&(x[0].0.file, x[0].0.end.0)];
         (
            roland_source_path_to_canon_path(&x[0].0.file, file_map).map(|x| x.unwrap()),
            Range {
               start: Position {
                  line: begin_line as u32,
                  character: begin_col as u32,
               },
               end: Position {
                  line: end_line as u32,
                  character: end_col as u32,
               },
            },
            x.into_iter()
               .flat_map(|x| rolandc_detail_to_diagnostic_detail(x, file_map, err_locations))
               .collect(),
         )
      }
      // Reporting this error with a bogus location is... well, it works, but can look strange.
      // The problem is that there is no good way to report an error that truly has no associated location.
      // See https://github.com/microsoft/language-server-protocol/issues/256
      ErrorLocation::NoLocation => (
         None,
         Range {
            start: Position { line: 0, character: 0 },
            end: Position { line: 0, character: 0 },
         },
         Vec::new(),
      ),
   };

   for came_from in re.came_from_stack {
      if let Some(d) = rolandc_detail_to_diagnostic_detail((came_from, "instantiation".into()), file_map, err_locations)
      {
         related_info.push(d);
      }
   }

   (
      report_path,
      Diagnostic {
         range,
         severity: Some(severity),
         message: re.message,
         related_information: Some(related_info),
         ..Default::default()
      },
   )
}

fn rolandc_detail_to_diagnostic_detail(
   y: (SourceInfo, String),
   file_map: &FileMap,
   err_locations: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
) -> Option<DiagnosticRelatedInformation> {
   let (begin_line, begin_col) = err_locations[&(y.0.file, y.0.begin.0)];
   let (end_line, end_col) = err_locations[&(y.0.file, y.0.end.0)];
   let path = roland_source_path_to_canon_path(&y.0.file, file_map).map(|x| x.unwrap());
   path.map(|sp| DiagnosticRelatedInformation {
      location: Location {
         uri: Uri::from_file_path(sp).unwrap(),
         range: Range {
            start: Position {
               line: begin_line as u32,
               character: begin_col as u32,
            },
            end: Position {
               line: end_line as u32,
               character: end_col as u32,
            },
         },
      },
      message: y.1,
   })
}

impl Backend {
   async fn compile_and_publish_diagnostics(&self, doc_uri: &Uri, doc_version: i32) {
      let (root_file_path, config) = {
         let mode = &*self.mode.read();
         let (root_file_path, target) = match mode {
            WorkspaceMode::LooseFiles => (doc_uri.to_file_path().unwrap(), Target::Wasi),
            WorkspaceMode::StdLib => (doc_uri.to_file_path().unwrap(), Target::Generic),
            WorkspaceMode::EntryPointAndTarget(x, t) => (Cow::Owned(x.clone()), *t),
         };
         let config = rolandc::CompilationConfig {
            target,
            include_std: !matches!(mode, WorkspaceMode::StdLib),
            i_am_std: matches!(mode, WorkspaceMode::StdLib),
            dump_debugging_info: false,
         };
         (root_file_path, config)
      };
      let (opened_versions, diagnostic_buckets) = {
         let mut ctx_ref = self.ctx.lock();
         let (opened_versions, touched_paths) = {
            let opened_files_l = self.opened_files.read();
            let mut touched_paths = Vec::new();
            let resolver = LSPFileResolver {
               file_map: &opened_files_l,
               touched_paths: &mut touched_paths,
            };
            let _ = rolandc::compile_for_errors(
               &mut ctx_ref,
               CompilationEntryPoint {
                  ep_path: root_file_path.to_path_buf(),
                  resolver,
               },
               &config,
            );
            (
               opened_files_l
                  .iter()
                  .map(|(key, v)| (key.clone(), v.1))
                  .collect::<HashMap<PathBuf, i32>>(),
               touched_paths,
            )
         };

         let mut diagnostic_buckets: HashMap<Option<PathBuf>, Vec<Diagnostic>> =
            HashMap::with_capacity(touched_paths.len() + 1);

         for path in touched_paths.into_iter() {
            // By doing this, we ensure that we will clear errors for files we touched that no longer have any issues
            diagnostic_buckets.insert(Some(path), Vec::new());
         }

         // This obj local allows the subsequent split borrow to succeed
         let obj = ctx_ref.deref_mut();
         let file_map = &obj.source_files;

         let err_location_map = obj
            .err_manager
            .map_all_err_locations_to_line_col::<false, true>(file_map);

         let errs = &mut obj.err_manager.errors;
         let warnings = &mut obj.err_manager.warnings;

         for err in errs.drain(..) {
            let (bucket, lsp_error) =
               roland_error_to_lsp_error(err, file_map, &err_location_map, DiagnosticSeverity::ERROR);
            diagnostic_buckets
               .entry(bucket)
               .or_insert_with(Vec::new)
               .push(lsp_error);
         }

         for warning in warnings.drain(..) {
            let (bucket, lsp_error) =
               roland_error_to_lsp_error(warning, file_map, &err_location_map, DiagnosticSeverity::WARNING);
            diagnostic_buckets
               .entry(bucket)
               .or_insert_with(Vec::new)
               .push(lsp_error);
         }

         (opened_versions, diagnostic_buckets)
      };

      for (pb, diagnostics) in diagnostic_buckets.into_iter() {
         let version = pb
            .as_ref()
            .map_or(Some(doc_version), |x| opened_versions.get(x).copied());
         let url = pb
            .map(|x| Uri::from_file_path(x).unwrap())
            .unwrap_or_else(|| doc_uri.clone());
         self.client.publish_diagnostics(url, diagnostics, version).await;
      }
   }
}

impl LanguageServer for Backend {
   async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
      if !params
         .capabilities
         .general
         .and_then(|x| x.position_encodings)
         .is_some_and(|x| x.contains(&PositionEncodingKind::UTF8))
      {
         return Err(Error {
            code: ErrorCode::InvalidParams,
            message: Cow::Borrowed(
               "The roland language server only supports UTF-8 position encoding, but the client did not advertise this capability.",
            ),
            data: None,
         });
      }
      // TODO: this just takes the first root path
      #[allow(clippy::never_loop)]
      for root_path in params
         .workspace_folders
         .unwrap_or_default()
         .into_iter()
         .flat_map(|x| x.uri.to_file_path().map(|x| x.to_path_buf()))
      {
         let mode = if root_path.join("cart.rol").exists() {
            if root_path.join(".microw8").exists() {
               self
                  .client
                  .log_message(MessageType::INFO, "detected microw8 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(root_path.join("cart.rol"), Target::Microw8)
            } else {
               self
                  .client
                  .log_message(MessageType::INFO, "detected wasm4 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(root_path.join("cart.rol"), Target::Wasm4)
            }
         } else if root_path.join("main.rol").exists() {
            if root_path.join(".amd64").exists() {
               self
                  .client
                  .log_message(MessageType::INFO, "detected amd64 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(root_path.join("main.rol"), Target::QbeFreestanding)
            } else {
               self
                  .client
                  .log_message(MessageType::INFO, "detected wasi project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(root_path.join("main.rol"), Target::Wasi)
            }
         } else if root_path.join(".i_assure_you_we're_std").exists() {
            self.client.log_message(MessageType::INFO, "detected stdlib").await;
            WorkspaceMode::StdLib
         } else {
            WorkspaceMode::LooseFiles
         };
         *self.mode.write() = mode;
         return Ok(InitializeResult {
            capabilities: ServerCapabilities {
               definition_provider: Some(OneOf::Right(DefinitionOptions {
                  work_done_progress_options: WorkDoneProgressOptions {
                     work_done_progress: None,
                  },
               })),
               text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
               position_encoding: Some(PositionEncodingKind::UTF8),
               ..Default::default()
            },
            ..Default::default()
         });
      }
      *self.mode.write() = WorkspaceMode::LooseFiles;
      Ok(InitializeResult {
         capabilities: ServerCapabilities {
            definition_provider: Some(OneOf::Right(DefinitionOptions {
               work_done_progress_options: WorkDoneProgressOptions {
                  work_done_progress: None,
               },
            })),
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
            position_encoding: Some(PositionEncodingKind::UTF8),
            ..Default::default()
         },
         ..Default::default()
      })
   }

   async fn initialized(&self, _: InitializedParams) {
      let version = option_env!("GIT_COMMIT").unwrap_or("unknown");
      self
         .client
         .log_message(MessageType::INFO, format!("rolandc server initialized! v{}", version))
         .await;
   }

   async fn shutdown(&self) -> Result<()> {
      Ok(())
   }

   async fn goto_definition(&self, params: GotoDefinitionParams) -> Result<Option<GotoDefinitionResponse>> {
      let given_document = params.text_document_position_params.text_document;
      let given_location = params.text_document_position_params.position;

      let Some(p) = given_document.uri.to_file_path() else {
         self
            .client
            .log_message(
               MessageType::WARNING,
               format!(
                  "Hopelessly bailing on document uri as we can't convert it to a local path: {:?}",
                  given_document.uri
               ),
            )
            .await;
         return Ok(None);
      };

      let Ok(canon_path) = std::fs::canonicalize(p) else {
         self
            .client
            .log_message(
               MessageType::WARNING,
               format!("Can't canonicalize path: {:?}", given_document.uri),
            )
            .await;
         return Ok(None);
      };

      let source_pos: SourcePosition = {
         let opened_files = self.opened_files.read();
         let buf = opened_files
            .get(&canon_path)
            .map_or("", |x| &x.0)
            .as_bytes();

         let start_of_line_idx = if given_location.line == 0 {
            0
         } else {
            match memchr::memchr_iter(b'\n', buf).nth((given_location.line - 1) as usize) {
               Some(nl_idx) => nl_idx + 1,
               None => return Ok(None),
            }
         };

         SourcePosition(start_of_line_idx + given_location.character as usize)
      };
      let ctx = self.ctx.lock();
      if let Some(si) = find_definition(source_pos, &canon_path, &ctx) {
         let mut res: HashMap<(SourcePath, usize), ExpandedErrorLocation> = HashMap::new();
         convert_positions_to_line_column::<false, _>(
            vec![si.end.0, si.begin.0],
            si.file,
            ctx.source_files.get_index(si.file.0).unwrap().1,
            &mut res,
         );
         let (start_line, start_col) = res[&(si.file, si.begin.0)];
         let (end_line, end_col) = res[&(si.file, si.begin.0)];
         let dest_range = Range {
            start: Position {
               line: start_line as u32,
               character: start_col as u32,
            },
            end: Position {
               line: end_line as u32,
               character: end_col as u32,
            },
         };
         let target_path = roland_source_path_to_canon_path(&si.file, &ctx.source_files);
         Ok(target_path.map(|x| {
            GotoDefinitionResponse::Link(vec![LocationLink {
               origin_selection_range: None,
               target_uri: Uri::from_file_path(x.unwrap()).unwrap(),
               target_range: dest_range,
               target_selection_range: dest_range,
            }])
         }))
      } else {
         Ok(None)
      }
   }

   async fn did_open(&self, params: DidOpenTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Some(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.insert(canon_path, (params.text_document.text, params.text_document.version));
         } else {
            self
               .client
               .log_message(MessageType::WARNING, format!("Can't canonicalize path: {:?}", doc_uri))
               .await;
         }
      } else {
         self
            .client
            .log_message(
               MessageType::WARNING,
               format!(
                  "Hopelessly bailing on document uri as we can't convert it to a local path: {:?}",
                  doc_uri
               ),
            )
            .await;
      }
      self
         .compile_and_publish_diagnostics(&doc_uri, params.text_document.version)
         .await;
   }

   async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Some(p) = doc_uri.to_file_path()
         && let Ok(canon_path) = std::fs::canonicalize(p)
      {
         let mut lock = self.opened_files.write();
         lock.insert(
            canon_path,
            (
               std::mem::take(&mut params.content_changes[0].text),
               params.text_document.version,
            ),
         );
      }
      self
         .compile_and_publish_diagnostics(&doc_uri, params.text_document.version)
         .await;
   }

   async fn did_close(&self, params: DidCloseTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Some(p) = doc_uri.to_file_path()
         && let Ok(canon_path) = std::fs::canonicalize(p)
      {
         let mut lock = self.opened_files.write();
         lock.remove(&canon_path);
      }
      self.client.publish_diagnostics(doc_uri, vec![], None).await;
   }
}

#[tokio::main]
async fn main() {
   let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
   let (service, socket) = LspService::new(|client| Backend {
      client,
      mode: RwLock::new(WorkspaceMode::LooseFiles),
      opened_files: RwLock::new(HashMap::new()),
      ctx: Mutex::new(CompilationContext::new()),
   });
   Server::new(stdin, stdout, socket).serve(service).await;
}
