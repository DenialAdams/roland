mod html_debug;
mod lex;
mod parse;
mod validator;

use clap::Clap;
use std::path::PathBuf;

#[derive(Clap)]
struct Opts {
   source_file: PathBuf,
   #[clap(short, long)]
   output: PathBuf,
}

fn main() {
   let opts: Opts = Opts::parse();
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
   html_debug::print_ast_as_html(&ast);
   if err_count > 0 {
      eprintln!("There were {} semantic errors, bailing", err_count);
      std::process::exit(1);
   }
   eprintln!("Next phase unimplemented");
   std::process::exit(1);
}
