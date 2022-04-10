#![warn(clippy::pedantic)]
#![allow(clippy::single_match_else)] // Not always an improvement in my opinion
#![allow(clippy::missing_panics_doc)] // We don't have any documentation

use rolandc::{CompilationContext, CompilationError, Target};
use std::io::Write;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::HtmlInputElement;

static mut COMPILATION_CTX: Option<CompilationContext> = None;

#[wasm_bindgen(start)]
pub fn start() {
   std::panic::set_hook(Box::new(console_error_panic_hook::hook));
   unsafe {
      COMPILATION_CTX = Some(CompilationContext::new());
   }
}

#[wasm_bindgen]
#[must_use]
pub fn compile_and_update_all(source_code: &str) -> Option<Vec<u8>> {
   let ctx = unsafe { COMPILATION_CTX.as_mut().unwrap() };
   let window = web_sys::window().unwrap();
   let document = window.document().unwrap();
   let output_frame = document.get_element_by_id("out_frame").unwrap();
   let ast_frame = document.get_element_by_id("ast_frame").unwrap();

   let do_constant_folding: HtmlInputElement = document
      .get_element_by_id("do_constant_folding")
      .unwrap()
      .dyn_into()
      .unwrap();

   let mut ast_out = Vec::new();
   let mut err_out = Vec::new();

   let compile_result = rolandc::compile(
      ctx,
      rolandc::CompilationEntryPoint::Buffer(source_code),
      &mut err_out,
      Some(&mut ast_out),
      do_constant_folding.checked(),
      Target::Wasi,
   );

   ctx.err_manager.write_out_errors(&mut err_out, &ctx.interner);

   if let Err(CompilationError::Semantic(err_count)) = compile_result.as_ref() {
      writeln!(err_out, "There were {} semantic errors, bailing", err_count).unwrap();
   } else if let Err(CompilationError::Internal) = compile_result.as_ref() {
      writeln!(err_out, "rolandc has encountered an internal error. *This is a bug in the compiler*, please file an issue on github with the problematic input.").unwrap();
   }

   let ast_s = String::from_utf8(ast_out).unwrap();
   ast_frame.set_inner_html(&ast_s);

   let err_s = String::from_utf8(err_out).ok();
   match compile_result.as_ref() {
      Ok(v) => Some(wat::parse_bytes(v).unwrap().into_owned()),
      Err(_) => {
         output_frame.set_text_content(err_s.as_deref());
         None
      }
   }
}
