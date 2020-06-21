mod lex;
mod parse;

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
   println!("{:?}", tokens);
   let ast = match parse::astify(tokens) {
      Err(()) => std::process::exit(1),
      Ok(v) => v,
   };
   eprintln!("Next phase unimplemented");
   std::process::exit(1);
}
