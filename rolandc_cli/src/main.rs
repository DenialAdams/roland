use rolandc::{CompilationError, Target};
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

const HTML_HEADER: &str = "<!DOCTYPE HTML>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\">
  <title>rolandc AST debug</title>
  <link rel=\"stylesheet\" href=\"./ast.css\">
</head>
<body>";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: PathBuf,
   output_html_ast: bool,
   skip_constant_folding: bool,
   wasm4: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   let opts = Opts {
      source_file: pargs.free_from_os_str(parse_path)?,
      output: pargs.value_from_os_str("--output", parse_path)?,
      output_html_ast: pargs.contains("--output-html-ast"),
      skip_constant_folding: pargs.contains("--skip-constant-folding"),
      wasm4: pargs.contains("--wasm4"),
   };

   Ok(opts)
}

fn main() {
   let mut opts = parse_args().unwrap();

   let target = if opts.wasm4 { Target::Wasm4 } else { Target::Wasi };

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

   let compile_result = rolandc::compile(
      &user_program_s,
      &mut err_stream_l,
      ast_out.as_mut(),
      !opts.skip_constant_folding,
      target,
   );
   if let Some(x) = ast_out.as_mut() {
      writeln!(x, "</body>\n</html>").unwrap()
   }

   let out_bytes = match compile_result {
      Ok(v) => v,
      Err(CompilationError::Lex) => std::process::exit(1),
      Err(CompilationError::Parse) => std::process::exit(1),
      Err(CompilationError::Semantic(err_count)) => {
         writeln!(err_stream_l, "There were {} semantic errors, bailing", err_count).unwrap();
         std::process::exit(1);
      }
   };

   if target == Target::Wasm4 {
      opts.output.set_extension("wasm");
   } else {
      opts.output.set_extension("wast");
   }
   let mut wasm_out = File::create(opts.output).unwrap();
   wasm_out.write_all(&out_bytes).unwrap();
}
