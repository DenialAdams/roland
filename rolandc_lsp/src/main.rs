use std::io::Write;

use parking_lot::Mutex;
use rolandc::error_handling::ErrorLocation;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use rolandc::*;

struct NulWriter {}

impl Write for NulWriter {
   fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
      Ok(buf.len())
   }

   fn flush(&mut self) -> std::io::Result<()> {
      Ok(())
   }
}

struct Backend {
   client: Client,
   ctx: Mutex<CompilationContext>,
}

impl Backend {
   fn get_diagnostics(&self, doc_uri: &Url, content: &str) -> Vec<Diagnostic> {
      let mut ctx_ref = self.ctx.lock();
         let _ = rolandc::compile_for_errors(
            &mut *ctx_ref,
            CompilationEntryPoint::Buffer(content),
            Target::Wasi,
         );
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
      self.client.log_message(MessageType::INFO, "server initialized!").await;
   }

   async fn did_open(&self, params: DidOpenTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      let doc_version = params.text_document.version;
      let content = params.text_document.text;
      let diagnostics = self.get_diagnostics(&doc_uri, &content);
      self
         .client
         .publish_diagnostics(doc_uri, diagnostics, Some(doc_version))
         .await;
   }

   async fn did_change(&self, params: DidChangeTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      let doc_version = params.text_document.version;
      let content = params.content_changes[0].text.as_str();
      let diagnostics = self.get_diagnostics(&doc_uri, content);
      self
         .client
         .publish_diagnostics(doc_uri, diagnostics, Some(doc_version))
         .await;
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
      ctx: Mutex::new(CompilationContext::new()),
   });
   Server::new(stdin, stdout, socket).serve(service).await;
}
