use std::io::Write;

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

#[derive(Debug)]
struct Backend {
   client: Client,
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

   async fn did_change(&self, params: DidChangeTextDocumentParams) {
      let doc_uri = params.text_document.uri;
      let doc_version = params.text_document.version;
      let content = params.content_changes[0].text.as_str();
      let hao: Option<&mut NulWriter> = None;
      let result = rolandc::compile(
         CompilationEntryPoint::Buffer(content),
         &mut NulWriter {},
         hao,
         true,
         Target::Wasi,
      );
      if result.is_err() {
         self
            .client
            .log_message(MessageType::INFO, "failed to compile changes")
            .await;
      } else {
         self
            .client
            .log_message(MessageType::INFO, "compiled changes successfully")
            .await;
      }
   }

   async fn shutdown(&self) -> Result<()> {
      Ok(())
   }
}

#[tokio::main]
async fn main() {
   let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
   let (service, socket) = LspService::new(|client| Backend { client });
   Server::new(stdin, stdout, socket).serve(service).await;
}
