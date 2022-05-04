use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::DerefMut;
use std::path::PathBuf;

use parking_lot::{Mutex, RwLock};
use rolandc::error_handling::{ErrorInfo, ErrorLocation};
use rolandc::interner::Interner;
use rolandc::source_info::SourcePath;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use rolandc::*;

struct LSPFileResolver<'a> {
   file_map: &'a HashMap<PathBuf, (String, i32)>,
   touched_paths: &'a mut Vec<PathBuf>,
}

impl<'a> FileResolver<'a> for LSPFileResolver<'a> {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<Cow<'a, str>> {
      let canon_path = std::fs::canonicalize(path)?;
      let resolved = if let Some(buf) = self.file_map.get(&canon_path) {
         Ok(Cow::Borrowed(buf.0.as_str()))
      } else {
         match std::fs::read_to_string(path) {
            Ok(s) => Ok(Cow::Owned(s)),
            Err(e) => Err(e),
         }
      };
      self.touched_paths.push(canon_path);
      resolved
   }
}

struct Backend {
   client: Client,
   opened_files: RwLock<HashMap<PathBuf, (String, i32)>>,
   ctx: Mutex<CompilationContext>,
}

fn roland_source_path_to_canon_path(source_path: &SourcePath, interner: &Interner) -> std::io::Result<PathBuf> {
   match source_path {
      SourcePath::Sandbox => unreachable!(), // No language server in the roland sandbox
      SourcePath::Std => unreachable!(), // This is possible to be hit while developing Roland. Oh well, punt for now
      SourcePath::File(str_id) => {
         let some_path = interner.lookup(*str_id);
         std::fs::canonicalize(some_path)
      }
   }
}

fn roland_error_to_lsp_error(re: ErrorInfo, interner: &Interner) -> (Option<PathBuf>, Diagnostic) {
   let (report_path, range, related_info) = match re.location {
      ErrorLocation::Simple(x) => (
         Some(roland_source_path_to_canon_path(&x.file, interner).unwrap()),
         Range {
            start: Position {
               line: x.begin.line as u32,
               character: x.begin.col as u32,
            },
            end: Position {
               line: x.end.line as u32,
               character: x.end.col as u32,
            },
         },
         None,
      ),
      ErrorLocation::WithDetails(x) => (
         Some(roland_source_path_to_canon_path(&x[0].0.file, interner).unwrap()),
         Range {
            start: Position {
               line: x[0].0.begin.line as u32,
               character: x[0].0.begin.col as u32,
            },
            end: Position {
               line: x[0].0.end.line as u32,
               character: x[0].0.end.col as u32,
            },
         },
         Some(
            x.into_iter()
               .map(|y| DiagnosticRelatedInformation {
                  location: Location {
                     uri: Url::from_file_path(roland_source_path_to_canon_path(&y.0.file, interner).unwrap()).unwrap(),
                     range: Range {
                        start: Position {
                           line: y.0.begin.line as u32,
                           character: y.0.begin.col as u32,
                        },
                        end: Position {
                           line: y.0.end.line as u32,
                           character: y.0.end.col as u32,
                        },
                     },
                  },
                  message: y.1,
               })
               .collect(),
         ),
      ),
      ErrorLocation::NoLocation => (
         None,
         Range {
            start: Position { line: 0, character: 0 },
            end: Position { line: 0, character: 0 },
         },
         None,
      ),
   };

   (
      report_path,
      Diagnostic {
         range,
         severity: Some(DiagnosticSeverity::ERROR),
         message: re.message,
         related_information: related_info,
         ..Default::default()
      },
   )
}

impl Backend {
   async fn compile_and_publish_diagnostics(&self, doc_uri: &Url, doc_version: i32) {
      let (opened_versions, diagnostic_buckets) = {
         let file_path = doc_uri.to_file_path().unwrap();
         let mut ctx_ref = self.ctx.lock();
         let (opened_versions, touched_paths) = {
            let opened_files_l = self.opened_files.read();
            let mut touched_paths = Vec::new();
            let resolver = LSPFileResolver {
               file_map: &opened_files_l,
               touched_paths: &mut touched_paths,
            };
            let _ = rolandc::compile_for_errors(
               &mut *ctx_ref,
               CompilationEntryPoint::PathResolving(file_path, resolver),
               Target::Wasi,
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
         let errs = &mut obj.err_manager.errors;
         let interner = &obj.interner;
         for err in errs.drain(..) {
            let (bucket, lsp_error) = roland_error_to_lsp_error(err, interner);
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
            .map(|x| Url::from_file_path(x).unwrap())
            .unwrap_or_else(|| doc_uri.clone());
         self.client.publish_diagnostics(url, diagnostics, version).await;
      }
   }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
   async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
      Ok(InitializeResult {
         capabilities: ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
            ..Default::default()
         },
         ..Default::default()
      })
   }

   async fn initialized(&self, _: InitializedParams) {
      self
         .client
         .log_message(MessageType::INFO, "rolandc server initialized!")
         .await;
   }

   async fn did_open(&self, params: DidOpenTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Ok(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.insert(canon_path, (params.text_document.text, params.text_document.version));
         } else {
            self
               .client
               .log_message(MessageType::WARNING, format!("Can't canonicalize path: {}", doc_uri))
               .await;
         }
      } else {
         self
            .client
            .log_message(
               MessageType::WARNING,
               format!(
                  "Hopelessly bailing on document uri as we can't convert it to a local path: {}",
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
      if let Ok(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.insert(
               canon_path,
               (
                  std::mem::take(&mut params.content_changes[0].text),
                  params.text_document.version,
               ),
            );
         }
      }
      self
         .compile_and_publish_diagnostics(&doc_uri, params.text_document.version)
         .await;
   }

   async fn did_close(&self, params: DidCloseTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Ok(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.remove(&canon_path);
         }
      }
      self.client.publish_diagnostics(doc_uri, vec![], None).await;
   }

   async fn shutdown(&self) -> Result<()> {
      Ok(())
   }
}

#[tokio::main]
async fn main() {
   let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
   let (service, socket) = LspService::new(|client| Backend {
      client,
      opened_files: RwLock::new(HashMap::new()),
      ctx: Mutex::new(CompilationContext::new()),
   });
   Server::new(stdin, stdout, socket).serve(service).await;
}
