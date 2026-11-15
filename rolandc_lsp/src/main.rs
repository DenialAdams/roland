#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::unwrap_or_default)] // I want to know exactly what is being called

use std::borrow::Cow;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use goto_definition::find_definition;
use parking_lot::RwLock;
use rolandc::error_handling::{
   ColumnCountingCodeUnits, ErrorInfo, ErrorLocation, ExpandedErrorLocation, convert_positions_to_line_column,
};
use rolandc::source_info::{SourceInfo, SourcePath, SourcePosition};
use rolandc::*;
use tokio::sync::Mutex;
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

#[cfg(target_env = "musl")]
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod goto_definition;

enum WorkspaceMode {
   LooseFiles,
   EntryPointAndTarget(PathBuf, Target),
   StdLib,
}

struct OpenedFile {
   text: String,
   versions: HashMap<Uri, i32>,
}

struct CompilerState {
   context: CompilationContext,
   published_uris: HashMap<PathBuf, Vec<Uri>>,
}

fn document_uris(path: &Path, opened_files: &HashMap<PathBuf, OpenedFile>) -> Vec<Uri> {
   if let Some(file) = opened_files.get(path) {
      file.versions.keys().cloned().collect()
   } else {
      vec![Uri::from_file_path(path).unwrap()]
   }
}

struct LSPFileResolver<'a> {
   file_map: &'a HashMap<PathBuf, OpenedFile>,
   diagnostic_buckets: &'a mut HashMap<PathBuf, Vec<Diagnostic>>,
}

impl FileResolver for LSPFileResolver<'_> {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<Cow<'static, str>> {
      self.diagnostic_buckets.entry(path.to_path_buf()).or_default();
      if let Some(buf) = self.file_map.get(path) {
         Ok(Cow::Owned(buf.text.clone()))
      } else {
         match std::fs::read_to_string(path) {
            Ok(s) => Ok(Cow::Owned(s)),
            Err(e) => Err(e),
         }
      }
   }

   fn canonicalize_path<'a>(&'a self, path: &'a Path) -> std::io::Result<Cow<'a, Path>> {
      if let Some((path, _)) = self.file_map.get_key_value(path) {
         Ok(Cow::Borrowed(path))
      } else {
         std::fs::canonicalize(path).map(Cow::Owned)
      }
   }
}

struct Backend {
   client: Client,
   mode: RwLock<WorkspaceMode>,
   column_encoding: RwLock<PositionEncodingKind>,
   opened_files: RwLock<HashMap<PathBuf, OpenedFile>>,
   ctx: Mutex<CompilerState>,
}

fn roland_source_path_to_file_path<'a>(source_path: &SourcePath, file_map: &'a FileMap) -> Option<&'a Path> {
   let ((path, is_std), _file_contents) = file_map.get_index(source_path.0).unwrap();
   if *is_std {
      // Hit when rolandc provides a reference to a standard library defined type
      return None;
   }
   Some(path)
}

fn roland_error_to_lsp_error(
   re: ErrorInfo,
   fallback_path: &Path,
   file_map: &FileMap,
   opened_files: &HashMap<PathBuf, OpenedFile>,
   err_locations: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
   severity: DiagnosticSeverity,
) -> (PathBuf, Diagnostic) {
   let (report_path, range, mut related_info) = match re.location {
      ErrorLocation::Simple(x) => {
         let (begin_line, begin_col) = err_locations[&(x.file, x.begin.0)];
         let (end_line, end_col) = err_locations[&(x.file, x.end.0)];
         (
            roland_source_path_to_file_path(&x.file, file_map),
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
            roland_source_path_to_file_path(&x[0].0.file, file_map),
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
               .flat_map(|x| rolandc_detail_to_diagnostic_detail(x, file_map, opened_files, err_locations))
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
      related_info.extend(rolandc_detail_to_diagnostic_detail(
         (came_from, "instantiation".into()),
         file_map,
         opened_files,
         err_locations,
      ));
   }

   (
      report_path.unwrap_or(fallback_path).to_path_buf(),
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
   opened_files: &HashMap<PathBuf, OpenedFile>,
   err_locations: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
) -> Vec<DiagnosticRelatedInformation> {
   let (begin_line, begin_col) = err_locations[&(y.0.file, y.0.begin.0)];
   let (end_line, end_col) = err_locations[&(y.0.file, y.0.end.0)];
   let Some(path) = roland_source_path_to_file_path(&y.0.file, file_map) else {
      return Vec::new();
   };
   document_uris(path, opened_files)
      .into_iter()
      .map(|uri| DiagnosticRelatedInformation {
         location: Location {
            uri,
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
         message: y.1.clone(),
      })
      .collect()
}

impl Backend {
   async fn compile_and_publish_diagnostics(&self, state: &mut CompilerState, changed_document_uri: &Uri) {
      let CompilerState {
         context: ctx,
         published_uris,
      } = state;
      let (root_file_path, config) = {
         let mode = &*self.mode.read();
         let (root_file_path, target) = match mode {
            WorkspaceMode::LooseFiles | WorkspaceMode::StdLib => {
               let opened_files = self.opened_files.read();
               let Some((path, _)) = opened_files
                  .iter()
                  .find(|(_, file)| file.versions.contains_key(changed_document_uri))
               else {
                  return;
               };
               let target = if matches!(mode, WorkspaceMode::LooseFiles) {
                  Target::Wasi
               } else {
                  Target::Generic
               };
               (path.clone(), target)
            }
            WorkspaceMode::EntryPointAndTarget(x, t) => (x.clone(), *t),
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
         let opened_files_l = self.opened_files.read();
         let mut diagnostic_buckets: HashMap<PathBuf, Vec<Diagnostic>> = HashMap::new();
         if matches!(*self.mode.read(), WorkspaceMode::EntryPointAndTarget(..)) {
            for path in published_uris.keys() {
               diagnostic_buckets.insert(path.clone(), Vec::new());
            }
         }
         let opened_versions = {
            let mut resolver = LSPFileResolver {
               file_map: &opened_files_l,
               diagnostic_buckets: &mut diagnostic_buckets,
            };
            let _ = rolandc::compile_for_errors(
               ctx,
               CompilationEntryPoint {
                  ep_path: root_file_path.clone(),
                  resolver: &mut resolver,
               },
               &config,
            );
            opened_files_l
               .values()
               .flat_map(|file| file.versions.iter().map(|(uri, version)| (uri.clone(), *version)))
               .collect::<HashMap<Uri, i32>>()
         };

         let file_map = &ctx.source_files;

         let err_location_map = if *self.column_encoding.read() == PositionEncodingKind::UTF8 {
            ctx.err_manager
               .map_all_err_locations_to_line_col::<{ ColumnCountingCodeUnits::Utf8 }, true>(file_map)
         } else {
            ctx.err_manager
               .map_all_err_locations_to_line_col::<{ ColumnCountingCodeUnits::Utf16 }, true>(file_map)
         };

         let errs = &mut ctx.err_manager.errors;
         let warnings = &mut ctx.err_manager.warnings;

         for err in errs.drain(..) {
            let (bucket, lsp_error) = roland_error_to_lsp_error(
               err,
               &root_file_path,
               file_map,
               &opened_files_l,
               &err_location_map,
               DiagnosticSeverity::ERROR,
            );
            diagnostic_buckets
               .entry(bucket)
               .or_insert_with(Vec::new)
               .push(lsp_error);
         }

         for warning in warnings.drain(..) {
            let (bucket, lsp_error) = roland_error_to_lsp_error(
               warning,
               &root_file_path,
               file_map,
               &opened_files_l,
               &err_location_map,
               DiagnosticSeverity::WARNING,
            );
            diagnostic_buckets
               .entry(bucket)
               .or_insert_with(Vec::new)
               .push(lsp_error);
         }

         let mut publications = HashMap::new();
         for (path, diagnostics) in diagnostic_buckets {
            let uris = document_uris(&path, &opened_files_l);
            for uri in &uris {
               publications.insert(uri.clone(), diagnostics.clone());
            }
            if let Some(previous) = published_uris.remove(&path) {
               for uri in previous {
                  publications.entry(uri).or_insert_with(Vec::new);
               }
            }
            if !diagnostics.is_empty() {
               published_uris.insert(path, uris);
            }
         }
         (opened_versions, publications)
      };

      for (url, diagnostics) in diagnostic_buckets.into_iter() {
         let version = opened_versions.get(&url).copied();
         self.client.publish_diagnostics(url, diagnostics, version).await;
      }
   }
}

impl LanguageServer for Backend {
   async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
      // Serialize configuration changes with document operations.
      let _ctx = self.ctx.lock().await;
      let chosen_column_encoding = if params
         .capabilities
         .general
         .and_then(|x| x.position_encodings)
         .is_some_and(|x| x.contains(&PositionEncodingKind::UTF8))
      {
         // fastest for rolandc to decode, since it stores text as utf-8
         // and can just subtract instead of counting utf-16 code units
         // this is pure hopium, vscode doesn't support this and never will.
         PositionEncodingKind::UTF8
      } else {
         // allegedly always supported
         PositionEncodingKind::UTF16
      };
      *self.column_encoding.write() = chosen_column_encoding.clone();

      // TODO: this just takes the first root path
      #[allow(clippy::never_loop)]
      for root_path in params
         .workspace_folders
         .unwrap_or_default()
         .into_iter()
         .flat_map(|x| x.uri.to_file_path().map(|x| x.to_path_buf()))
      {
         let mode = if let Ok(entrypoint) = std::fs::canonicalize(root_path.join("cart.rol")) {
            if root_path.join(".microw8").exists() {
               self
                  .client
                  .log_message(MessageType::INFO, "detected microw8 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(entrypoint, Target::Microw8)
            } else {
               self
                  .client
                  .log_message(MessageType::INFO, "detected wasm4 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(entrypoint, Target::Wasm4)
            }
         } else if let Ok(entrypoint) = std::fs::canonicalize(root_path.join("main.rol")) {
            if root_path.join(".amd64").exists() {
               self
                  .client
                  .log_message(MessageType::INFO, "detected amd64 project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(entrypoint, Target::QbeFreestanding)
            } else {
               self
                  .client
                  .log_message(MessageType::INFO, "detected wasi project")
                  .await;
               WorkspaceMode::EntryPointAndTarget(entrypoint, Target::Wasi)
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
               position_encoding: Some(chosen_column_encoding),
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
            position_encoding: Some(chosen_column_encoding),
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
      let state = self.ctx.lock().await;
      let ctx = &state.context;
      let given_document = params.text_document_position_params.text_document;
      let doc_uri = given_document.uri;
      let given_location = params.text_document_position_params.position;

      let (canon_path, source_pos) = {
         let opened_files = self.opened_files.read();
         let Some((canon_path, file)) = opened_files
            .iter()
            .find(|(_, file)| file.versions.contains_key(&doc_uri))
         else {
            return Ok(None);
         };
         let buf = &file.text;
         let start_of_line_idx = if given_location.line == 0 {
            0
         } else {
            match memchr::memchr_iter(b'\n', buf.as_bytes()).nth(given_location.line as usize - 1) {
               Some(nl_idx) => nl_idx + 1,
               None => return Ok(None),
            }
         };
         let tail = &buf[start_of_line_idx..];
         let end = memchr::memchr(b'\n', tail.as_bytes()).unwrap_or(tail.len());
         let line = tail[..end].trim_end_matches('\r');
         let character = given_location.character as usize;
         let offset = if *self.column_encoding.read() == PositionEncodingKind::UTF8 {
            character.min(line.len())
         } else {
            let mut units = 0;
            let mut offset = line.len();
            for (byte, ch) in line.char_indices() {
               if units == character {
                  offset = byte;
                  break;
               }
               units += ch.len_utf16();
            }
            offset
         };
         (canon_path.clone(), SourcePosition(start_of_line_idx + offset))
      };
      if let Some(si) = find_definition(source_pos, &canon_path, ctx) {
         let mut res: HashMap<(SourcePath, usize), ExpandedErrorLocation> = HashMap::new();
         if *self.column_encoding.read() == PositionEncodingKind::UTF8 {
            convert_positions_to_line_column::<{ ColumnCountingCodeUnits::Utf8 }, _>(
               vec![si.end.0, si.begin.0],
               si.file,
               ctx.source_files.get_index(si.file.0).unwrap().1,
               &mut res,
            );
         } else {
            convert_positions_to_line_column::<{ ColumnCountingCodeUnits::Utf16 }, _>(
               vec![si.end.0, si.begin.0],
               si.file,
               ctx.source_files.get_index(si.file.0).unwrap().1,
               &mut res,
            );
         }
         let (start_line, start_col) = res[&(si.file, si.begin.0)];
         let (end_line, end_col) = res[&(si.file, si.end.0)];
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
         let target_path = roland_source_path_to_file_path(&si.file, &ctx.source_files);
         Ok(target_path.map(|path| {
            GotoDefinitionResponse::Link(
               document_uris(path, &self.opened_files.read())
                  .into_iter()
                  .map(|uri| LocationLink {
                     origin_selection_range: None,
                     target_uri: uri,
                     target_range: dest_range,
                     target_selection_range: dest_range,
                  })
                  .collect(),
            )
         }))
      } else {
         Ok(None)
      }
   }

   async fn did_open(&self, params: DidOpenTextDocumentParams) {
      let mut ctx = self.ctx.lock().await;
      let doc_uri = params.text_document.uri;
      if let Some(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            let file = lock.entry(canon_path).or_insert_with(|| OpenedFile {
               text: String::new(),
               versions: HashMap::new(),
            });
            file.versions.insert(doc_uri.clone(), params.text_document.version);
            file.text = params.text_document.text;
         } else {
            self
               .client
               .log_message(MessageType::WARNING, format!("Can't canonicalize path: {:?}", doc_uri))
               .await;
            return;
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
         return;
      }
      self.compile_and_publish_diagnostics(&mut ctx, &doc_uri).await;
   }

   async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
      // We use full synchronization, so we only need to look at the last change
      let Some(change) = params.content_changes.pop() else {
         return;
      };
      let mut ctx = self.ctx.lock().await;
      let doc_uri = params.text_document.uri;
      {
         let mut files = self.opened_files.write();
         let Some(file) = files.values_mut().find(|file| file.versions.contains_key(&doc_uri)) else {
            return;
         };
         let version = file.versions.get_mut(&doc_uri).unwrap();
         if params.text_document.version <= *version {
            return;
         }
         *version = params.text_document.version;
         file.text = change.text;
      }
      self.compile_and_publish_diagnostics(&mut ctx, &doc_uri).await;
   }

   async fn did_close(&self, params: DidCloseTextDocumentParams) {
      // Wait for earlier diagnostic publications before closing (or else they could be republished erroneously)
      // This is a bad solution - we should improve this in the future such that closing a tab always
      // clears diagnostics immediately and if a compilation comes in afterwards it would just know (somehow)
      // not to publish those diagnostics.
      let mut state = self.ctx.lock().await;
      let doc_uri = params.text_document.uri;
      self.opened_files.write().retain(|_, file| {
         file.versions.remove(&doc_uri);
         !file.versions.is_empty()
      });
      state.published_uris.retain(|_, uris| {
         uris.retain(|uri| *uri != doc_uri);
         !uris.is_empty()
      });
      self.client.publish_diagnostics(doc_uri, vec![], None).await;
   }
}

#[tokio::main]
async fn main() {
   let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
   let (service, socket) = LspService::new(|client| Backend {
      client,
      column_encoding: RwLock::new(PositionEncodingKind::UTF8),
      mode: RwLock::new(WorkspaceMode::LooseFiles),
      opened_files: RwLock::new(HashMap::new()),
      ctx: Mutex::new(CompilerState {
         context: CompilationContext::new(),
         published_uris: HashMap::new(),
      }),
   });
   Server::new(stdin, stdout, socket).serve(service).await;
}
