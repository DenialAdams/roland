use clap::Clap;
use rolandc::CompilationError;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

const HTML_HEADER: &'static str = "<!DOCTYPE HTML>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\">
  <title>rolandc AST debug</title>
  <link rel=\"stylesheet\" href=\"./ast.css\">
</head>
<body>";

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
      let mut writer = BufWriter::new(out_f);
      writeln!(writer, "{}", HTML_HEADER).unwrap();
      Some(writer)
   } else {
      None
   };

   let err_stream = std::io::stderr();
   let mut err_stream_l = err_stream.lock();

   let compile_result = rolandc::compile(&user_program_s, &mut err_stream_l, ast_out.as_mut());
   ast_out.as_mut().map(|x| writeln!(x, "</body>\n</html>").unwrap());

   let out_bytes = match compile_result {
      Ok(v) => v,
      Err(CompilationError::Lex) => std::process::exit(1),
      Err(CompilationError::Parse) => std::process::exit(1),
      Err(CompilationError::Semantic(err_count)) => {
         writeln!(err_stream_l, "There were {} semantic errors, bailing", err_count).unwrap();
         std::process::exit(1);
      }
   };

   opts.output.set_extension("wast");
   let mut wasm_out = File::create(opts.output).unwrap();
   wasm_out.write_all(&out_bytes).unwrap();
}
