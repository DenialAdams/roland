#![warn(clippy::pedantic)]
#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::unnecessary_wraps)] // False positives
#![allow(clippy::too_many_lines)] // A procedure should have however many lines as it needs. More procedures is not better.

mod assemble;

use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::fmt::Display;
use std::path::PathBuf;
use std::process::{Command, ExitStatus};

use rolandc::{BaseTarget, CompilationContext, CompilationEntryPoint, FileResolver, Target};

use crate::assemble::{assemble_bytes, assemble_file, invoke_qbe};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[cfg(target_env = "musl")]
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

const HELP: &str = r"
Usage: rolandc (source.rol) [OPTION]*

Valid boolean options are:
--wasm4   | Links the WASM-4 standard library and emits a WASM-4 cart
--microw8 | Links the microw8 standard library and emits a microw8 cart
--wasi    | Links the standard library and emits a binary for use with a WASI-compliant runtime
--amd64   | Links the standard library and emits a static binary for use on an x86_64 linux system

Valid options with arguments are:
--output (output_file.wasm) | Specify the name of the output file
--target (target_name)      | Specify the compilation target
--linker (linker name)      | Specify the linker to use when linking the final binary on amd64

Other modes:
--help    | Prints this message
--version | Prints the git commit this executable was built from";

#[derive(Debug)]
struct Opts {
   source_file: PathBuf,
   output: Option<PathBuf>,
   target: Option<Target>,
   linker: Option<OsString>,
   dump_debugging_info: bool,
   preserve_intermediate_outputs: bool,
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
      "amd64" | "amd64-freestanding" => Target::QbeFreestanding,
      "amd64-host" => Target::QbeHost,
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
      ("--amd64", Target::QbeFreestanding),
      ("--amd64-host", Target::QbeHost),
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
      preserve_intermediate_outputs: pargs.contains("--preserve-intermediate-outputs"),
      output: pargs.opt_value_from_os_str("--output", parse_path)?,
      linker: pargs.opt_value_from_str("--linker")?,
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

impl FileResolver for CliFileResolver {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'static, str>> {
      std::fs::read_to_string(path).map(Cow::Owned)
   }

   fn requires_canonicalization(&self) -> bool {
      true
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

   let compile_result = rolandc::compile(
      &mut ctx,
      CompilationEntryPoint {
         ep_path: opts.source_file.clone(),
         resolver: &mut CliFileResolver {},
      },
      &config,
   );

   ctx.err_manager
      .write_out_errors(&mut err_stream_l, true, &ctx.source_files);

   let Ok(compile_result) = compile_result else {
      std::process::exit(1);
   };

   let output_path = if let Some(v) = &opts.output {
      v.clone()
   } else {
      let mut output_path = opts.source_file.clone();
      if config.target.base() == BaseTarget::Qbe {
         output_path.set_extension("");
      } else {
         output_path.set_extension("wasm");
      }
      output_path
   };

   if config.target.base() == BaseTarget::Wasm {
      std::fs::write(&output_path, compile_result.program_bytes).unwrap();
   } else if let Err(e) = compile_qbe(
      opts.linker.as_ref().map(AsRef::as_ref),
      &compile_result.program_bytes,
      output_path,
      compile_result.link_requests,
      config.target == Target::QbeFreestanding,
      opts.preserve_intermediate_outputs,
   ) {
      use std::io::Write;
      writeln!(err_stream_l, "Failed to compile produced IR to binary: {}", e).unwrap();
      std::process::exit(1);
   }
}

enum QbeCompilationError {
   AsInvocation(std::io::Error),
   AsExecution(ExitStatus),
   LdInvocation(std::io::Error),
   LdExecution(Option<ExitStatus>),
   QbeInvocation(std::io::Error),
   QbeExecution(ExitStatus),
}

impl Display for QbeCompilationError {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
         QbeCompilationError::AsExecution(exit_status) => {
            write!(f, "as failed to execute with code {}", exit_status)
         }
         QbeCompilationError::AsInvocation(io_err) => {
            write!(f, "Failed to invoke as: {}", io_err)
         }
         QbeCompilationError::LdExecution(Some(exit_status)) => {
            write!(f, "linker failed to execute with code {}", exit_status)
         }
         QbeCompilationError::LdExecution(None) => {
            write!(f, "linker failed to execute")
         }
         QbeCompilationError::LdInvocation(io_err) => {
            write!(f, "Failed to invoke linker: {}", io_err)
         }
         QbeCompilationError::QbeExecution(exit_status) => {
            write!(f, "qbe failed to execute with code {}", exit_status)
         }
         QbeCompilationError::QbeInvocation(io_err) => {
            write!(f, "Failed to invoke qbe: {}", io_err)
         }
      }
   }
}

#[allow(clippy::ref_option)]
fn compile_qbe(
   linker: Option<&OsStr>,
   ssa_bytes: &[u8],
   final_path: PathBuf,
   link_requests: impl IntoIterator<Item = impl AsRef<str>>,
   freestanding: bool,
   preserve_intermediate_outputs: bool,
) -> std::result::Result<(), QbeCompilationError> {
   if preserve_intermediate_outputs {
      std::fs::write(final_path.with_extension("ssa"), ssa_bytes).unwrap();
   }
   let asm_result = invoke_qbe(ssa_bytes)?;
   let asm_path = asm_result.path();
   if preserve_intermediate_outputs {
      std::fs::copy(asm_path, final_path.with_extension("s")).unwrap();
   }
   let program_object_path = assemble_file(asm_path)?;
   let syscall_object_path = assemble_bytes(include_bytes!("syscall.s"))?;

   if freestanding {
      let start_object_path = assemble_bytes(include_bytes!("start.s"))?;

      let mut linker_args: Vec<OsString> = vec![
         "-nostdlib".into(),
         "--no-dynamic-linker".into(),
         "-static".into(),
         "-pie".into(),
         "-o".into(),
         final_path.into(),
         program_object_path.path().into(),
         syscall_object_path.path().into(),
         start_object_path.path().into(),
      ];

      linker_args.push("--start-group".into());
      for link_request in link_requests {
         linker_args.push(format!("-l{}", link_request.as_ref()).into());
      }
      linker_args.push("--end-group".into());

      #[cfg(target_os = "linux")]
      if linker.is_none() {
         let args = {
            let arg_fn = || linker_args.iter().map(|s| s.to_str().unwrap());

            let mut args = libwild::Args::new(arg_fn).unwrap();
            args.parse(arg_fn).unwrap();
            args
         };

         return libwild::run(args).map_err(|e| {
            libwild::error::report_error(&e);
            QbeCompilationError::LdExecution(None)
         });
      }

      let mut ld_command = Command::new(linker.unwrap_or(OsStr::new("ld")));
      ld_command.args(linker_args);

      match ld_command.status() {
         Ok(stat) if stat.success() => Ok(()),
         Ok(stat) => Err(QbeCompilationError::LdExecution(Some(stat))),
         Err(e) => Err(QbeCompilationError::LdInvocation(e)),
      }
   } else {
      let mut cc_command = Command::new("cc");
      cc_command.arg("-o");
      cc_command.args(&[
         final_path,
         program_object_path.path().into(),
         syscall_object_path.path().into(),
      ]);
      if let Some(specified_linker) = linker {
         cc_command.arg(format!("-fuse-ld={}", specified_linker.to_str().unwrap()));
      }
      for link_request in link_requests {
         cc_command.arg(format!("-l{}", link_request.as_ref()));
      }

      match cc_command.status() {
         Ok(stat) if stat.success() => Ok(()),
         Ok(stat) => Err(QbeCompilationError::LdExecution(Some(stat))),
         Err(e) => Err(QbeCompilationError::LdInvocation(e)),
      }
   }
}
