#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::single_match_else)] // Not always an improvement in my opinion
#![allow(clippy::missing_panics_doc)] // We don't have any documentation
#![allow(clippy::missing_errors_doc)] // We don't have any documentation

use std::io::Write;

use rolandc::{CompilationContext, CompilationError, FileResolver};
use wasm_bindgen::prelude::*;

static mut COMPILATION_CTX: Option<CompilationContext> = None;

#[wasm_bindgen(start)]
pub fn start() {
   std::panic::set_hook(Box::new(console_error_panic_hook::hook));
   unsafe {
      COMPILATION_CTX = Some(CompilationContext::new());
   }
}

struct PlaygroundFileResolver;

impl<'a> FileResolver<'a> for PlaygroundFileResolver {
   fn resolve_path(&mut self, _path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      unreachable!()
   }
}

#[wasm_bindgen]
pub fn compile_wasm4(source_code: &str) -> Result<Vec<u8>, String> {
   let ctx = unsafe { COMPILATION_CTX.as_mut().unwrap() };

   let mut err_out = Vec::new();

   let config = rolandc::CompilationConfig {
      target: rolandc::Target::Wasm4,
      include_std: true,
      i_am_std: false,
   };

   let compile_result =
      rolandc::compile::<PlaygroundFileResolver>(ctx, rolandc::CompilationEntryPoint::Playground(source_code), &config);

   ctx.err_manager.write_out_errors(&mut err_out, &ctx.interner);

   compile_result.map_err(|_| String::from_utf8_lossy(&err_out).into_owned())
}

#[wasm_bindgen]
#[must_use]
pub fn compile_and_update_all(source_code: &str) -> Option<Vec<u8>> {
   let ctx = unsafe { COMPILATION_CTX.as_mut().unwrap() };
   let window = web_sys::window().unwrap();
   let document = window.document().unwrap();
   let output_frame = document.get_element_by_id("out_frame").unwrap();

   let mut err_out = Vec::new();

   let config = rolandc::CompilationConfig {
      target: rolandc::Target::Wasi,
      include_std: true,
      i_am_std: false,
   };

   let compile_result =
      rolandc::compile::<PlaygroundFileResolver>(ctx, rolandc::CompilationEntryPoint::Playground(source_code), &config);

   ctx.err_manager.write_out_errors(&mut err_out, &ctx.interner);

   if let Err(CompilationError::Internal) = compile_result.as_ref() {
      writeln!(err_out, "rolandc has encountered an internal error. *This is a bug in the compiler*, please file an issue on github with the problematic input.").unwrap();
   }

   let err_s = String::from_utf8(err_out).ok();
   match compile_result.as_ref() {
      Ok(v) => Some(wat::parse_bytes(v).unwrap().into_owned()),
      Err(_) => {
         output_frame.set_text_content(err_s.as_deref());
         None
      }
   }
}
