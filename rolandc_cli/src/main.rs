#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::match_same_arms)] // Sometimes I find this more clear (when it's just calling something)
#![allow(clippy::unnecessary_wraps)] // False positives

use std::borrow::Cow;
use std::error::Error;
use std::path::PathBuf;
use std::process::Command;

use rolandc::{CompilationContext, CompilationEntryPoint, FileResolver, Target};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

const HELP: &str = r"
Usage: rolandc (source.rol) [OPTION]*

Valid boolean options are:
--wasm4   | Links the WASM-4 standard library and emits a WASM-4 cart
--microw8 | Links the microw8 standard library and emits a microw8 cart
--wasi    | Links the full roland standard library and emits a binary for use with a WASI-compliant runtime
--amd64   | (EXPERIMENTAL)

Valid options with arguments are:
--output (output_file.wasm) | Specify the name of the output file
--target (target_name)      | Specify the compilation target

Other modes:
--help    | Prints this message
--version | Prints the git commit this executable was built from";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: Option<PathBuf>,
   target: Option<Target>,
   dump_debugging_info: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_target(s: &std::ffi::OsStr) -> Result<Target, &'static str> {
   let mut lower = s.to_string_lossy().into_owned();
   lower.make_ascii_lowercase();
   Ok(match lower.as_str() {
      "wasm4" | "wasm-4" => Target::Wasm4,
      "wasi" => Target::Wasi,
      "microw8" => Target::Microw8,
      "amd64" => Target::Qbe,
      _ => return Err("Unrecognized target"),
   })
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

   let mut target: Option<Target> = None;

   let target_arr = [
      ("--wasm4", Target::Wasm4),
      ("--microw8", Target::Microw8),
      ("--wasi", Target::Wasi),
      ("--amd64", Target::Qbe),
   ];

   for (opt, pot_target) in target_arr {
      if pargs.contains(opt) {
         if target.is_some() {
            eprintln!("Only one target may be specified");
            std::process::exit(1);
         }

         target = Some(pot_target);
      }
   }

   if let Some(t) = pargs.opt_value_from_os_str("--target", parse_target)? {
      if target.is_some() {
         eprintln!("Only one target may be specified");
         std::process::exit(1);
      }

      target = Some(t);
   }

   let opts = Opts {
      target,
      dump_debugging_info: pargs.contains("--dump-debugging-info"),
      output: pargs.opt_value_from_os_str("--output", parse_path)?,
      source_file: pargs.free_from_os_str(parse_path)?,
   };

   let remaining_args = pargs.finish();

   if !remaining_args.is_empty() {
      let remaining_args_unicode: Vec<_> = remaining_args.iter().map(|x| x.to_string_lossy()).collect();
      eprintln!("Unrecognized arguments: '{}'", remaining_args_unicode.join("', '"));
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
         eprintln!("Argument parsing error: {}", e);
         eprintln!("{}", HELP);
         std::process::exit(1);
      }
   };

   let err_stream = std::io::stderr();
   let mut err_stream_l = err_stream.lock();

   let mut ctx = CompilationContext::new();
   let config = rolandc::CompilationConfig {
      target: opts.target.unwrap_or(Target::Wasi),
      include_std: true,
      i_am_std: false,
      dump_debugging_info: opts.dump_debugging_info,
   };

   let compile_result = rolandc::compile::<CliFileResolver>(
      &mut ctx,
      CompilationEntryPoint::PathResolving(opts.source_file.clone(), CliFileResolver {}),
      &config,
   );

   ctx.err_manager.write_out_errors(&mut err_stream_l, &ctx.interner);

   let Ok(out_bytes) = compile_result else {
      std::process::exit(1);
   };

   let output_path = if let Some(v) = opts.output {
      v
   } else {
      let mut output_path = opts.source_file.clone();
      if config.target == Target::Qbe {
         output_path.set_extension("ssa");
      } else {
         output_path.set_extension("wasm");
      }
      output_path
   };

   std::fs::write(&output_path, out_bytes).unwrap();

   if config.target == Target::Qbe {
      if let Err(e) = compile_qbe(output_path) {
         use std::io::Write;
         writeln!(err_stream_l, "Failed to compile produced IR to binary: {}", e).unwrap();
         std::process::exit(1);
      }
   }
}

fn compile_qbe(mut ssa_path: PathBuf) -> std::result::Result<(), Box<dyn Error>> {
   let mut asm_path = ssa_path.clone();
   asm_path.set_extension("s");
   let qbe_stat = Command::new("qbe").arg("-o").arg(&asm_path).arg(&ssa_path).status()?;
   if !qbe_stat.success() {
      return Err(format!("QBE failed to execute with code {}", qbe_stat).into());
   }
   ssa_path.set_extension("");
   let cc_stat = Command::new("cc").arg("-o").arg(ssa_path).arg(&asm_path).status()?;
   if !cc_stat.success() {
      return Err(format!("cc failed to execute with code {}", qbe_stat).into());
   }
   Ok(())
}
