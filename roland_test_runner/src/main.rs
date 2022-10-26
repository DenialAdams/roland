#![feature(local_key_cell_methods)]

#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::unwrap_or_else_default)] // I want to know exactly what is being called

struct CliFileResolver {}
// todo: unpasta?
impl<'a> FileResolver<'a> for CliFileResolver {
   fn resolve_path(&mut self, path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      std::fs::read_to_string(path).map(Cow::Owned)
   }
}

use std::borrow::Cow;
use std::cell::RefCell;
use std::env;
use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};
use std::sync::Mutex;

use os_pipe::pipe;
use rayon::prelude::*;
use rolandc::{CompilationContext, CompilationEntryPoint, FileResolver};
use similar_asserts::SimpleDiff;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

enum TestFailureReason {
   TestingNothing,
   ExpectedCompilationFailure,
   ExpectedCompilationSuccess,
   FailedToRunExecutable,
   MismatchedExecutionOutput(String, String),
   MismatchedCompilationErrorOutput(String, String, File),
}

struct Opts {
   test_path: PathBuf,
   tc_path: Option<PathBuf>,
   overwrite_error_files: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   let cli_path = pargs.opt_value_from_os_str("--cli", parse_path)?;

   let opts = Opts {
      test_path: pargs.free_from_os_str(parse_path)?,
      tc_path: cli_path,
      overwrite_error_files: pargs.contains("--overwrite-error-files"),
   };

   let remaining_args = pargs.finish();

   if !remaining_args.is_empty() {
      let remaining_args_unicode: Vec<_> = remaining_args.iter().map(|x| x.to_string_lossy()).collect();
      eprintln!("Unrecognized arugments: '{}'", remaining_args_unicode.join("', '"));
      std::process::exit(1);
   }

   Ok(opts)
}

thread_local! {
   pub static COMPILATION_CTX: RefCell<CompilationContext> = RefCell::new(CompilationContext::new());
}

fn main() -> Result<(), &'static str> {
   let mut err_color = ColorSpec::new();
   err_color.set_fg(Some(Color::Red));
   err_color.set_intense(true);
   let mut pass_color = ColorSpec::new();
   pass_color.set_fg(Some(Color::Green));
   pass_color.set_intense(true);
   let mut reset_color = ColorSpec::new();
   reset_color.set_fg(None);
   reset_color.set_intense(false);

   let opts = parse_args().unwrap();

   env::set_current_dir(&opts.test_path).unwrap();

   let current_dir = env::current_dir().unwrap();
   let mut result_dir = current_dir.clone();
   result_dir.push("results");

   let output_mutex: Mutex<(u64, u64)> = Mutex::new((0, 0));

   let entries: Vec<PathBuf> = current_dir
      .read_dir()
      .unwrap()
      .map(|x| x.unwrap().path())
      .filter(|e| e.extension().and_then(OsStr::to_str) == Some("rol"))
      .collect();

   entries.par_iter().for_each(|entry| {
      let tc_output = match &opts.tc_path {
         Some(tc_path) => Command::new(tc_path).arg(entry.file_name().unwrap()).output().unwrap(),
         None => COMPILATION_CTX.with_borrow_mut(|ctx| {
            let compile_result = rolandc::compile::<CliFileResolver>(
               ctx,
               CompilationEntryPoint::PathResolving(entry.file_name().unwrap().into(), CliFileResolver {}),
               rolandc::Target::Wasi,
            );

            let mut stderr = Vec::new();

            ctx.err_manager.write_out_errors(&mut stderr, &ctx.interner);

            let status = match compile_result {
               Ok(bytes) => {
                  let mut wat_file = entry.clone();
                  wat_file.set_extension("wat");
                  std::fs::write(wat_file, bytes).unwrap();
                  ExitStatus::from_raw(0)
               }
               Err(_) => ExitStatus::from_raw(1),
            };

            Output {
               status,
               stdout: vec![],
               stderr,
            }
         }),
      };
      let test_ok = test_result(&tc_output, entry, &result_dir);
      let mut lock = output_mutex.lock().unwrap();
      match test_ok {
         Ok(()) => {
            lock.0 += 1;
            let stdout = StandardStream::stdout(ColorChoice::Auto);
            let mut out_handle = stdout.lock();
            let _ = out_handle.set_color(&reset_color);
            write!(out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            let _ = out_handle.set_color(&pass_color);
            writeln!(out_handle, "ok").unwrap();
            let _ = out_handle.set_color(&reset_color);
         }
         Err(reason) => {
            lock.1 += 1;
            let stderr = StandardStream::stderr(ColorChoice::Auto);
            let mut out_handle = stderr.lock();
            let _ = out_handle.set_color(&reset_color);
            writeln!(out_handle, "--------------------").unwrap();
            write!(out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            let _ = out_handle.set_color(&err_color);
            writeln!(out_handle, "FAILED").unwrap();
            let _ = out_handle.set_color(&reset_color);
            match reason {
               TestFailureReason::TestingNothing => {
                  if !opts.overwrite_error_files {
                     writeln!(out_handle, "There was no test specified for this input.").unwrap();
                  }

                  let actual = String::from_utf8_lossy(&tc_output.stderr);

                  writeln!(out_handle, "\ncompilation output:").unwrap();
                  writeln!(out_handle, "```").unwrap();
                  writeln!(out_handle, "{}", actual).unwrap();
                  writeln!(out_handle, "```").unwrap();

                  if opts.overwrite_error_files {
                     let mut err_file_handle = open_result_file(&result_dir, entry, "err", true).unwrap();
                     err_file_handle.write_all(actual.as_bytes()).unwrap();
                     err_file_handle.set_len(actual.as_bytes().len() as u64).unwrap();
                     writeln!(out_handle, "Created test compilation error output.").unwrap();
                  }
               }
               TestFailureReason::ExpectedCompilationFailure => {
                  writeln!(out_handle, "Compilation was supposed to fail, but it succeeded.").unwrap();
               }
               TestFailureReason::ExpectedCompilationSuccess => {
                  writeln!(out_handle, "Compilation was supposed to succeed, but it failed:").unwrap();
                  writeln!(out_handle, "```").unwrap();
                  writeln!(out_handle, "{}", String::from_utf8_lossy(&tc_output.stderr)).unwrap();
                  writeln!(out_handle, "```").unwrap();
               }
               TestFailureReason::FailedToRunExecutable => {
                  writeln!(
                     out_handle,
                     "Compilation seemingly succeeded, but the executable failed to run. Is wasmtime installed?"
                  )
                  .unwrap();
               }
               TestFailureReason::MismatchedExecutionOutput(expected, actual) => {
                  writeln!(
                     out_handle,
                     "Compiled OK, but execution of the program produced a different result than expected:"
                  )
                  .unwrap();
                  print_diff(&mut out_handle, &expected, &actual);
               }
               TestFailureReason::MismatchedCompilationErrorOutput(expected, actual, mut err_file_handle) => {
                  if opts.overwrite_error_files {
                     err_file_handle.seek(SeekFrom::Start(0)).unwrap();
                     err_file_handle.write_all(actual.as_bytes()).unwrap();
                     err_file_handle.set_len(actual.as_bytes().len() as u64).unwrap();
                     print_diff(&mut out_handle, &expected, &actual);
                     writeln!(out_handle, "Updated test compilation error output.").unwrap();
                  } else {
                     writeln!(
                        out_handle,
                        "Failed to compile, but the compilation error was different than expected:"
                     )
                     .unwrap();
                     print_diff(&mut out_handle, &expected, &actual);
                  }
               }
            }
            writeln!(out_handle, "--------------------").unwrap();
         }
      }
   });

   let stdout = StandardStream::stdout(ColorChoice::Auto);
   let mut out_handle = stdout.lock();

   let lock = output_mutex.lock().unwrap();

   let _ = out_handle.set_color(&pass_color);
   write!(out_handle, "{} ", lock.0).unwrap();
   let _ = out_handle.set_color(&reset_color);
   if lock.0 == 1 {
      write!(out_handle, "success, ").unwrap();
   } else {
      write!(out_handle, "successes, ").unwrap();
   }
   let _ = out_handle.set_color(&err_color);
   write!(out_handle, "{} ", lock.1).unwrap();
   let _ = out_handle.set_color(&reset_color);
   if lock.1 == 1 {
      writeln!(out_handle, "failure").unwrap();
   } else {
      writeln!(out_handle, "failures").unwrap();
   }
   Ok(())
}

fn print_diff<W: WriteColor>(t: &mut W, expected: &str, actual: &str) {
   writeln!(t, "{}", SimpleDiff::from_str(expected, actual, "expected", "actual")).unwrap();
}

fn test_result(tc_output: &Output, t_file_path: &Path, result_dir: &Path) -> Result<(), TestFailureReason> {
   let mut expected_comptime_output = String::new();
   let mut err_handle: Option<File> = None;
   {
      let err_file = open_result_file(result_dir, t_file_path, "err", false);

      match err_file {
         Ok(mut f) => {
            f.read_to_string(&mut expected_comptime_output).unwrap();
            err_handle = Some(f);
         }
         Err(e) if e.kind() == io::ErrorKind::NotFound => {}
         Err(e) => panic!("{}", e),
      }
   }

   let mut expected_runtime_output: Option<String> = None;
   {
      let out_file = open_result_file(result_dir, t_file_path, "out", false);

      match out_file {
         Ok(mut f) => {
            let mut s = String::new();
            f.read_to_string(&mut s).unwrap();
            expected_runtime_output = Some(s);
         }
         Err(e) if e.kind() == io::ErrorKind::NotFound => {}
         Err(e) => panic!("{}", e),
      }
   }

   if expected_comptime_output.is_empty() && expected_runtime_output.is_none() {
      return Err(TestFailureReason::TestingNothing);
   }

   let stderr_text = String::from_utf8_lossy(&tc_output.stderr);

   if tc_output.status.success() {
      if !expected_comptime_output.is_empty() && stderr_text.is_empty() {
         return Err(TestFailureReason::ExpectedCompilationFailure);
      } else if !expected_comptime_output.is_empty() && stderr_text != expected_comptime_output {
         return Err(TestFailureReason::MismatchedCompilationErrorOutput(
            expected_comptime_output,
            stderr_text.into_owned(),
            err_handle.unwrap(),
         ));
      }

      let ero = expected_runtime_output.unwrap_or_else(String::new);

      // Execute the program
      let mut prog_path = t_file_path.to_path_buf();
      prog_path.set_extension("wat");

      let mut prog_output = String::new();
      {
         let mut prog_command = Command::new("wasmtime");
         prog_command.arg(prog_path.as_os_str());
         // It's desirable to combine stdout and stderr, so an output test can test either or both
         let mut prog_output_stream = {
            let (reader, writer) = pipe().unwrap();
            let writer_clone = writer.try_clone().unwrap();
            prog_command.stdout(writer);
            prog_command.stderr(writer_clone);
            reader
         };
         let mut handle = match prog_command.spawn() {
            Ok(v) => v,
            Err(_) => {
               return Err(TestFailureReason::FailedToRunExecutable);
            }
         };
         drop(prog_command);
         prog_output_stream.read_to_string(&mut prog_output).unwrap();
         handle.wait().unwrap();
      };

      if prog_output != ero {
         return Err(TestFailureReason::MismatchedExecutionOutput(ero, prog_output));
      }

      std::fs::remove_file(prog_path).unwrap();
   } else if expected_runtime_output.is_some() {
      return Err(TestFailureReason::ExpectedCompilationSuccess);
   } else if !expected_comptime_output.is_empty() && stderr_text != expected_comptime_output {
      return Err(TestFailureReason::MismatchedCompilationErrorOutput(
         expected_comptime_output,
         stderr_text.into_owned(),
         err_handle.unwrap(),
      ));
   }

   Ok(())
}

fn open_result_file(result_dir: &Path, entry: &Path, extension: &'static str, create_new: bool) -> io::Result<File> {
   let mut out_name = entry.to_path_buf();
   out_name.set_extension(extension);
   let mut out_path = result_dir.to_path_buf();
   out_path.push(out_name.file_name().unwrap());
   OpenOptions::new()
      .read(true)
      .write(true)
      .append(false)
      .create_new(create_new)
      .open(out_path)
}
