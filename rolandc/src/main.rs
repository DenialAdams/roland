mod html_debug;
mod lex;
mod parse;
mod validator;
mod wasm;

use clap::Clap;
use std::io::Write;
use std::fs::File;
use std::path::PathBuf;

#[derive(Clap)]
struct Opts {
   source_file: PathBuf,
   #[clap(long)]
   ouput_html_ast: bool,
   #[clap(short, long)]
   output: PathBuf,
}

fn main() {
   let mut opts: Opts = Opts::parse();
   let s = std::fs::read_to_string(opts.source_file).unwrap();
   let tokens = match lex::lex(s) {
      Err(()) => std::process::exit(1),
      Ok(v) => v,
   };
   let mut ast = match parse::astify(tokens) {
      Err(()) => std::process::exit(1),
      Ok(v) => v,
   };
   let err_count = validator::type_and_check_validity(&mut ast);
   if opts.ouput_html_ast {
      html_debug::print_ast_as_html(&ast);
   }
   if err_count > 0 {
      eprintln!("There were {} semantic errors, bailing", err_count);
      std::process::exit(1);
   }
   let wasm_text = wasm::emit_wasm(&ast);
   println!("{}", String::from_utf8(wasm_text.clone()).unwrap());
   //let wasm_bin = wabt::wat2wasm(wasm_text).unwrap();
   opts.output.set_extension("wast");
   let mut wasm_out = File::create(opts.output).unwrap();
   wasm_out.write_all(&wasm_text).unwrap();
}
