#![warn(clippy::pedantic)]
#![allow(clippy::match_same_arms)] // Sometimes I find this more clear (when it's just calling something)
#![allow(clippy::unnecessary_wraps)] // False positives

use rolandc::{CompilationContext, CompilationEntryPoint, CompilationError, Target, FileResolver};
use std::borrow::Cow;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

const HELP: &str = r"
Usage: rolandc (source.rol) [OPTION]+

Valid boolean options are:
--wasm4

Valid options with arguments are:
--output (output_file.wasm)";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: Option<PathBuf>,
   wasm4: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   if pargs.contains("--help") {
      eprintln!("{}", HELP);

      std::process::exit(0);
   }

   let opts = Opts {
      wasm4: pargs.contains("--wasm4"),
      output: pargs.opt_value_from_os_str("--output", parse_path)?,
      source_file: pargs.free_from_os_str(parse_path)?,
   };

   let remaining_args = pargs.finish();

   if !remaining_args.is_empty() {
      let remaining_args_unicode: Vec<_> = remaining_args.iter().map(|x| x.to_string_lossy()).collect();
      eprintln!("Unrecognized arugments: '{}'", remaining_args_unicode.join("', '"));
      eprintln!("{}", HELP);
   }

   Ok(opts)
}

struct CliFileResolver {
}

impl<'a> FileResolver<'a> for CliFileResolver {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      std::fs::read_to_string(path).map(Cow::Owned)
   }
}


fn main() {
   let opts = match parse_args() {
      Ok(v) => v,
      Err(e) => {
         eprintln!("We didn't understand the arguments you provided: {}", e);
         eprintln!("{}", HELP);
         std::process::exit(1);
      }
   };

   let err_stream = std::io::stderr();
   let mut err_stream_l = err_stream.lock();

   let target = if opts.wasm4 { Target::Wasm4 } else { Target::Wasi };

   let mut ctx = CompilationContext::new();
   let compile_result = rolandc::compile::<CliFileResolver>(&mut ctx, CompilationEntryPoint::PathResolving(opts.source_file.clone(), CliFileResolver{}), target);

   ctx.err_manager.write_out_errors(&mut err_stream_l, &ctx.interner);

   let out_bytes = match compile_result {
      Ok(v) => v,
      Err(CompilationError::Lex) => std::process::exit(1),
      Err(CompilationError::Parse) => std::process::exit(1),
      Err(CompilationError::Semantic(err_count)) => {
         writeln!(err_stream_l, "There were {} semantic errors, bailing", err_count).unwrap();
         std::process::exit(1);
      }
      Err(CompilationError::Io) => std::process::exit(1),
      Err(CompilationError::Internal) => {
         writeln!(err_stream_l, "rolandc has encountered an internal error. *This is a bug in the compiler*, please file an issue on github with the problematic input.").unwrap();
         std::process::exit(1);
      }
   };

   let output_path = if let Some(v) = opts.output {
      v
   } else {
      let mut output_path = opts.source_file.clone();
      match target {
         Target::Wasm4 => output_path.set_extension("wasm"),
         Target::Wasi => output_path.set_extension("wat"),
      };
      output_path
   };

   let mut wasm_out = File::create(output_path).unwrap();
   wasm_out.write_all(&out_bytes).unwrap();
}
