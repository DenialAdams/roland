#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::missing_panics_doc)] // We don't have any documentation
#![allow(clippy::missing_errors_doc)] // We don't have any documentation

use std::sync::Mutex;

use rolandc::{CompilationContext, FileResolver};
use wasm_bindgen::prelude::*;

static COMPILATION_CTX: Mutex<Option<CompilationContext>> = Mutex::new(None);

#[wasm_bindgen(start)]
pub fn start() {
   std::panic::set_hook(Box::new(console_error_panic_hook::hook));
   *COMPILATION_CTX.lock().unwrap() = Some(CompilationContext::new());
}

struct PlaygroundFileResolver;

impl<'a> FileResolver<'a> for PlaygroundFileResolver {
   fn resolve_path(&mut self, _path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      unreachable!()
   }
}

#[wasm_bindgen]
pub fn compile_wasm4(source_code: &str) -> Result<Vec<u8>, String> {
   let mut lock = COMPILATION_CTX.lock().unwrap();
   let ctx = lock.as_mut().unwrap();

   let mut err_out = Vec::new();

   let config = rolandc::CompilationConfig {
      target: rolandc::Target::Wasm4,
      include_std: true,
      i_am_std: false,
      dump_debugging_info: false,
   };

   let compile_result =
      rolandc::compile::<PlaygroundFileResolver>(ctx, rolandc::CompilationEntryPoint::Playground(source_code), &config);

   ctx.err_manager.write_out_errors(&mut err_out, &ctx.interner);

   compile_result.map_err(|_| String::from_utf8_lossy(&err_out).into_owned())
}

#[wasm_bindgen]
pub struct CompilationOutput {
   bytes: Vec<u8>,
   disasm: String,
}

#[wasm_bindgen]
impl CompilationOutput {
   #[must_use]
   #[wasm_bindgen(getter)]
   pub fn disasm(&self) -> String {
      self.disasm.clone()
   }

   #[must_use]
   #[wasm_bindgen(getter)]
   pub fn bytes(&self) -> Vec<u8> {
      self.bytes.clone()
   }
}

#[wasm_bindgen]
#[must_use]
pub fn compile_and_update_all(source_code: &str) -> Option<CompilationOutput> {
   let mut lock = COMPILATION_CTX.lock().unwrap();
   let ctx = lock.as_mut().unwrap();
   let window = web_sys::window().unwrap();
   let document = window.document().unwrap();
   let output_frame = document.get_element_by_id("out_frame").unwrap();

   let mut err_out = Vec::new();

   let config = rolandc::CompilationConfig {
      target: rolandc::Target::Wasi,
      include_std: true,
      i_am_std: false,
      dump_debugging_info: false,
   };

   let compile_result =
      rolandc::compile::<PlaygroundFileResolver>(ctx, rolandc::CompilationEntryPoint::Playground(source_code), &config);

   ctx.err_manager.write_out_errors(&mut err_out, &ctx.interner);

   if let Ok(v) = compile_result {
      let disasm = wasmprinter::print_bytes(v.as_slice()).unwrap();
      Some(CompilationOutput { bytes: v, disasm })
   } else {
      output_frame.set_text_content(String::from_utf8(err_out).ok().as_deref());
      None
   }
}
