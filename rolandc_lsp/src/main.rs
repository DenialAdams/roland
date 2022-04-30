use std::borrow::Cow;
use std::collections::{HashMap};
use std::path::PathBuf;

use parking_lot::{Mutex, RwLock};
use rolandc::error_handling::ErrorLocation;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use rolandc::*;

struct LSPFileResolver<'a> {
   file_map: &'a HashMap<PathBuf, String>,
}

impl<'a> FileResolver<'a> for LSPFileResolver<'a> {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<Cow<'a, str>> {
      let canon_path = std::fs::canonicalize(path)?;
      if let Some(buf) = self.file_map.get(&canon_path) {
         Ok(Cow::Borrowed(buf.as_str()))
      } else {
         match std::fs::read_to_string(path) {
            Ok(s) => Ok(Cow::Owned(s)),
            Err(e) => Err(e),
         }
      }
   }
}

struct Backend {
   client: Client,
   opened_files: RwLock<HashMap<PathBuf, String>>,
   ctx: Mutex<CompilationContext>,
}

impl Backend {
   fn get_diagnostics(&self, doc_uri: &Url) -> Vec<Diagnostic> {
      let file_path = doc_uri.to_file_path().unwrap();
      let mut ctx_ref = self.ctx.lock();
      {
         let opened_files_l = self.opened_files.read();
         let resolver = LSPFileResolver {
            file_map: &opened_files_l,
         };
         let _ = rolandc::compile_for_errors(&mut *ctx_ref, CompilationEntryPoint::PathResolving(file_path, resolver), Target::Wasi);
      }
      ctx_ref
         .err_manager
         .errors
         .drain(..)
         .map(|x| {
            let (range, related_info) = match x.location {
               ErrorLocation::Simple(x) => (
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
                              uri: doc_uri.clone(),
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
                  Range {
                     start: Position { line: 0, character: 0 },
                     end: Position { line: 0, character: 0 },
                  },
                  None,
               ),
            };

            Diagnostic {
               range,
               severity: Some(DiagnosticSeverity::ERROR),
               message: x.message,
               related_information: related_info,
               ..Default::default()
            }
         })
         .collect()
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
      self.client.log_message(MessageType::INFO, "rolandc server initialized!").await;
   }

   async fn did_open(&self, params: DidOpenTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Ok(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.insert(canon_path, params.text_document.text);
         } else {
            self.client.log_message(MessageType::WARNING, format!("Can't canonicalize path: {}", doc_uri)).await;
         }
      } else {
         self.client.log_message(MessageType::WARNING, format!("Hopelessly bailing on document uri as we can't convert it to a local path: {}", doc_uri)).await;
      }
      let doc_version = params.text_document.version;
      let diagnostics = self.get_diagnostics(&doc_uri);
      self
         .client
         .publish_diagnostics(doc_uri, diagnostics, Some(doc_version))
         .await;
   }

   async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      if let Ok(p) = doc_uri.to_file_path() {
         if let Ok(canon_path) = std::fs::canonicalize(p) {
            let mut lock = self.opened_files.write();
            lock.insert(canon_path, std::mem::take(&mut params.content_changes[0].text));
         }
      }
      let doc_version = params.text_document.version;
      let diagnostics = self.get_diagnostics(&doc_uri);
      self
         .client
         .publish_diagnostics(doc_uri, diagnostics, Some(doc_version))
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
