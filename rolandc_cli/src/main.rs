#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::match_same_arms)] // Sometimes I find this more clear (when it's just calling something)
#![allow(clippy::unnecessary_wraps)] // False positives

use std::borrow::Cow;
use std::io::Write;
use std::path::PathBuf;

use rolandc::{CompilationContext, CompilationEntryPoint, CompilationError, FileResolver, Target};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

const HELP: &str = r"
Usage: rolandc (source.rol) [OPTION]*

Valid boolean options are:
--wasm4 | Links the WASM-4 standard library and emits a WASM-4 cart
--microw8 | Links the microw8 standard library and emits a microw8 cart

Valid options with arguments are:
--output (output_file.wasm) | Specify the name of the output file

Other modes:
--help | Prints this message
--version | Prints the git commit this executable was built from";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: Option<PathBuf>,
   wasm4: bool,
   microw8: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   if pargs.contains("--help") {
      println!("{}", HELP);

      std::process::exit(0);
   } else if pargs.contains("--version") {
      let version = option_env!("GIT_COMMIT").unwrap_or("unknown");
      println!("rolandc {}", version);

      std::process::exit(0);
   }

   let opts = Opts {
      wasm4: pargs.contains("--wasm4"),
      microw8: pargs.contains("--microw8"),
      output: pargs.opt_value_from_os_str("--output", parse_path)?,
      source_file: pargs.free_from_os_str(parse_path)?,
   };

   let remaining_args = pargs.finish();

   if !remaining_args.is_empty() {
      let remaining_args_unicode: Vec<_> = remaining_args.iter().map(|x| x.to_string_lossy()).collect();
      eprintln!("Unrecognized arugments: '{}'", remaining_args_unicode.join("', '"));
      eprintln!("{}", HELP);
      std::process::exit(1);
   }

   Ok(opts)
}

struct CliFileResolver {}

impl<'a> FileResolver<'a> for CliFileResolver {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      std::fs::read_to_string(path).map(Cow::Owned)
   }
}

fn main() {
   #[cfg(feature = "dhat-heap")]
   let _profiler = dhat::Profiler::new_heap();

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

   // this doesn't scale :) we'll change the CLI at some point to accept --target <x>!
   let target = match (opts.microw8, opts.wasm4) {
      (true, true) => {
         eprintln!("--wasm4 must not be specified with --microw8");
         std::process::exit(1);
      }
      (true, false) => Target::Microw8,
      (false, true) => Target::Wasm4,
      (false, false) => Target::Wasi,
   };

   let mut ctx = CompilationContext::new();
   let config = rolandc::CompilationConfig {
      target,
      include_std: true,
      i_am_std: false,
   };

   let compile_result = rolandc::compile::<CliFileResolver>(
      &mut ctx,
      CompilationEntryPoint::PathResolving(opts.source_file.clone(), CliFileResolver {}),
      &config,
   );

   ctx.err_manager.write_out_errors(&mut err_stream_l, &ctx.interner);

   let out_bytes = match compile_result {
      Ok(v) => v,
      Err(CompilationError::Lex) => std::process::exit(1),
      Err(CompilationError::Parse) => std::process::exit(1),
      Err(CompilationError::Semantic) => std::process::exit(1),
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
         Target::Wasm4 | Target::Microw8 => output_path.set_extension("wasm"),
         Target::Wasi | Target::Lib => output_path.set_extension("wat"),
      };
      output_path
   };

   std::fs::write(output_path, out_bytes).unwrap();
}
