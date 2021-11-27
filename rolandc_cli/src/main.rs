use rolandc::{CompilationError, Target};
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

const HTML_HEADER: &str = r#"<!DOCTYPE HTML>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>rolandc AST debug</title>
  <link rel="stylesheet" href="./ast.css">
</head>
<body>"#;

const HELP: &str = r"
Usage: rolandc (source.rol) [OPTION]+

Valid boolean options are:
--wasm4
--skip-constant-folding
--output-html-ast

Valid options with arguments are:
--output (output_file.wasm)";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: Option<PathBuf>,
   output_html_ast: bool,
   skip_constant_folding: bool,
   wasm4: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   if pargs.contains("--help") {
      println!("{}", HELP);

      std::process::exit(0);
   }

   let opts = Opts {
      output_html_ast: pargs.contains("--output-html-ast"),
      skip_constant_folding: pargs.contains("--skip-constant-folding"),
      wasm4: pargs.contains("--wasm4"),
      output: pargs.opt_value_from_os_str("--output", parse_path)?,
      source_file: pargs.free_from_os_str(parse_path)?,
   };

   Ok(opts)
}

fn main() {
   let err_stream = std::io::stderr();
   let mut err_stream_l = err_stream.lock();

   let opts = match parse_args() {
      Ok(v) => v,
      Err(e) => {
         writeln!(err_stream_l, "We didn't understand the arguments you provided: {}", e).unwrap();
         println!("{}", HELP);
         std::process::exit(1);
      }
   };

   let target = if opts.wasm4 { Target::Wasm4 } else { Target::Wasi };

   let user_program_s = if let Ok(s) = std::fs::read_to_string(&opts.source_file) {
      s
   } else {
      writeln!(
         err_stream_l,
         "Failed to open the file '{}'",
         opts.source_file.to_string_lossy()
      )
      .unwrap();
      std::process::exit(1);
   };

   let mut ast_out: Option<BufWriter<File>> = if opts.output_html_ast {
      let out_f = File::create("ast.html").unwrap();
      let mut writer = BufWriter::new(out_f);
      writeln!(writer, "{}", HTML_HEADER).unwrap();
      Some(writer)
   } else {
      None
   };

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

   let output_path = if let Some(v) = opts.output {
      v
   } else {
      let mut output_path = opts.source_file.clone();
      match target {
         Target::Wasm4 => output_path.set_extension("wasm"),
         Target::Wasi => output_path.set_extension("wast"),
      };
      output_path
   };

   let mut wasm_out = File::create(output_path).unwrap();
   wasm_out.write_all(&out_bytes).unwrap();
}
