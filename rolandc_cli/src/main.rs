use clap::Clap;
use rolandc::CompilationError;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

#[derive(Clap)]
struct Opts {
   source_file: PathBuf,
   #[clap(long)]
   output_html_ast: bool,
   #[clap(short, long)]
   output: PathBuf,
}

fn main() {
   let mut opts: Opts = Opts::parse();
   let user_program_s = std::fs::read_to_string(opts.source_file).unwrap();
   let mut ast_out: Option<BufWriter<File>> = if opts.output_html_ast {
      let out_f = File::create("ast.html").unwrap();
      Some(BufWriter::new(out_f))
   } else {
      None
   };

   let compile_result = rolandc::compile(&user_program_s, ast_out.as_mut());

   let out_bytes = match compile_result {
      Ok(v) => v,
      Err(CompilationError::Lex) => unimplemented!(),
      Err(CompilationError::Parse) => unimplemented!(),
      Err(CompilationError::Sematic(err_count)) => {
         eprintln!("There were {} semantic errors, bailing", err_count);
         std::process::exit(1);
      }
   };

   opts.output.set_extension("wast");
   let mut wasm_out = File::create(opts.output).unwrap();
   wasm_out.write_all(&out_bytes).unwrap();
}
