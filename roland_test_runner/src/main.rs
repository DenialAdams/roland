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
use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
#[cfg(not(target_os = "windows"))]
use std::os::unix::process::ExitStatusExt;
#[cfg(target_os = "windows")]
use std::os::windows::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

use os_pipe::pipe;
use rayon::prelude::*;
use rolandc::{CompilationContext, CompilationEntryPoint, FileResolver};
use similar_asserts::SimpleDiff;

enum TestFailureReason {
   TestingNothing(File),
   ExpectedCompilationSuccess,
   FailedToRunExecutable,
   MismatchedExecutionOutput(String, String),
   MismatchedCompilationErrorOutput(String, TestDetails),
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

fn bold_green<W: Write>(w: &mut W) -> std::io::Result<()> {
   write!(w, "\x1b[1;32m")
}

fn bold_red<W: Write>(w: &mut W) -> std::io::Result<()> {
   write!(w, "\x1b[1;31m")
}

fn color_reset<W: Write>(w: &mut W) -> std::io::Result<()> {
   write!(w, "\x1b[0m")
}

fn recursive_push_test_files(p: &Path, buf: &mut Vec<PathBuf>) {
   for sub_p in p.read_dir().unwrap() {
      let sub_p = sub_p.unwrap().path();
      if sub_p.extension().and_then(OsStr::to_str) == Some("rol") {
         buf.push(sub_p);
      } else if sub_p.is_dir() {
         recursive_push_test_files(&sub_p, buf);
      }
   }
}

fn main() -> Result<(), &'static str> {
   let opts = parse_args().unwrap();

   let entries: Vec<PathBuf> = if opts.test_path.is_dir() {
      let mut entries = vec![];
      recursive_push_test_files(&opts.test_path, &mut entries);
      entries
   } else {
      vec![opts.test_path]
   };

   let successes = AtomicU64::new(0);
   let failures = AtomicU64::new(0);
   let output_lock = Mutex::new(());

   let config = rolandc::CompilationConfig {
      target: rolandc::Target::Wasi,
      include_std: true,
      i_am_std: false,
   };

   entries.par_iter().for_each(|entry| {
      let tc_output = match &opts.tc_path {
         Some(tc_path) => Command::new(tc_path).arg(entry.clone()).output().unwrap(),
         None => COMPILATION_CTX.with_borrow_mut(|ctx| {
            let compile_result = rolandc::compile::<CliFileResolver>(
               ctx,
               CompilationEntryPoint::PathResolving(entry.clone(), CliFileResolver {}),
               &config,
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
      let test_ok = test_result(&tc_output, entry);
      // prevents stdout and stderr from mixing
      let _ol = output_lock.lock();
      match test_ok {
         Ok(()) => {
            successes.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let mut out_handle = std::io::stdout().lock();
            color_reset(&mut out_handle).unwrap();
            write!(out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            bold_green(&mut out_handle).unwrap();
            writeln!(out_handle, "ok").unwrap();
            color_reset(&mut out_handle).unwrap();
         }
         Err(reason) => {
            failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let mut out_handle = std::io::stderr().lock();
            color_reset(&mut out_handle).unwrap();
            writeln!(out_handle, "--------------------").unwrap();
            write!(out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            bold_red(&mut out_handle).unwrap();
            writeln!(out_handle, "FAILED").unwrap();
            color_reset(&mut out_handle).unwrap();
            match reason {
               TestFailureReason::TestingNothing(mut file) => {
                  if !opts.overwrite_error_files {
                     writeln!(out_handle, "There was no test specified for this input.").unwrap();
                  }

                  let actual = String::from_utf8_lossy(&tc_output.stderr);

                  writeln!(out_handle, "\ncompilation output:").unwrap();
                  writeln!(out_handle, "```").unwrap();
                  writeln!(out_handle, "{}", actual).unwrap();
                  writeln!(out_handle, "```").unwrap();

                  if opts.overwrite_error_files {
                     file.write_all(b"__END__\n").unwrap();
                     file.write_all(b"compile:\n").unwrap();
                     file.write_all(actual.as_bytes()).unwrap();
                     let current_position = file.stream_position().unwrap();
                     file.set_len(current_position).unwrap();
                     writeln!(out_handle, "Created test compilation error output.").unwrap();
                  }
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
               TestFailureReason::MismatchedCompilationErrorOutput(actual, mut test_details) => {
                  if opts.overwrite_error_files {
                     // file should have been sunk to the correct point
                     test_details.file.write_all(b"compile:\n").unwrap();
                     test_details.file.write_all(actual.as_bytes()).unwrap();
                     if let Some(r) = test_details.result.run_output {
                        test_details.file.write_all(b"\nrun:\n").unwrap();
                        test_details.file.write_all(r.as_bytes()).unwrap();
                     }
                     let current_position = test_details.file.stream_position().unwrap();
                     test_details.file.set_len(current_position).unwrap();
                     print_diff(
                        &mut out_handle,
                        test_details.result.compile_output.as_ref().map_or("", |x| x.as_str()),
                        &actual,
                     );
                     writeln!(out_handle, "Updated test compilation error output.").unwrap();
                  } else {
                     writeln!(
                        out_handle,
                        "Failed to compile, but the compilation error was different than expected:"
                     )
                     .unwrap();
                     print_diff(
                        &mut out_handle,
                        test_details.result.compile_output.as_ref().map_or("", |x| x.as_str()),
                        &actual,
                     );
                  }
               }
            }
            writeln!(out_handle, "--------------------").unwrap();
         }
      }
   });

   let successes = successes.load(Ordering::Relaxed);
   let failures = failures.load(Ordering::Relaxed);

   let mut out_handle = std::io::stdout().lock();

   bold_green(&mut out_handle).unwrap();
   write!(out_handle, "{} ", successes).unwrap();
   color_reset(&mut out_handle).unwrap();
   if successes == 1 {
      write!(out_handle, "success, ").unwrap();
   } else {
      write!(out_handle, "successes, ").unwrap();
   }
   bold_red(&mut out_handle).unwrap();
   write!(out_handle, "{} ", failures).unwrap();
   color_reset(&mut out_handle).unwrap();
   if failures == 1 {
      writeln!(out_handle, "failure").unwrap();
   } else {
      writeln!(out_handle, "failures").unwrap();
   }
   Ok(())
}

fn print_diff<W: Write>(t: &mut W, expected: &str, actual: &str) {
   writeln!(t, "{}", SimpleDiff::from_str(expected, actual, "expected", "actual")).unwrap();
}

fn test_result(tc_output: &Output, t_file_path: &Path) -> Result<(), TestFailureReason> {
   let td = extract_test_data(t_file_path);

   if td.result.compile_output.is_none() && td.result.run_output.is_none() {
      return Err(TestFailureReason::TestingNothing(td.file));
   }

   let stderr_text = String::from_utf8_lossy(&tc_output.stderr);

   if tc_output.status.success() {
      if td
         .result
         .compile_output
         .as_ref()
         .map_or(false, |x| x.as_str() != stderr_text)
      {
         return Err(TestFailureReason::MismatchedCompilationErrorOutput(
            stderr_text.into_owned(),
            td,
         ));
      }

      let ero = td.result.run_output.unwrap_or_else(String::new);

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
   } else if td.result.run_output.is_some() {
      return Err(TestFailureReason::ExpectedCompilationSuccess);
   } else if td
      .result
      .compile_output
      .as_ref()
      .map_or(false, |x| x.as_str() != stderr_text)
   {
      return Err(TestFailureReason::MismatchedCompilationErrorOutput(
         stderr_text.into_owned(),
         td,
      ));
   }

   Ok(())
}

struct TestDetails {
   file: File,
   result: ExpectedTestResult,
}

struct ExpectedTestResult {
   compile_output: Option<String>,
   run_output: Option<String>,
}

fn extract_test_data(entry: &Path) -> TestDetails {
   let mut opened = OpenOptions::new().read(true).write(true).open(entry).unwrap();

   let mut s = String::new();
   opened.read_to_string(&mut s).unwrap();

   let anchor = "__END__\n";
   let anchor_location = s.rfind(anchor);
   let test_output = if let Some(loc) = anchor_location {
      opened.seek(SeekFrom::Start((loc + anchor.len()) as u64)).unwrap();
      parse_test_content(&s[loc + anchor.len()..])
   } else {
      // This file doesn't seem to have any test content.
      // We'll see if there is an adjacent .result file
      let mut result_name = entry.to_path_buf();
      result_name.set_extension("result");
      if !result_name.exists() {
         // Alright, this file just has no test specified
         return TestDetails {
            file: opened,
            result: ExpectedTestResult {
               compile_output: None,
               run_output: None,
            },
         };
      }
      opened = OpenOptions::new().read(true).write(true).open(result_name).unwrap();
      s.clear();
      opened.read_to_string(&mut s).unwrap();

      opened.seek(SeekFrom::Start(0)).unwrap();
      parse_test_content(&s)
   };

   TestDetails {
      file: opened,
      result: test_output,
   }
}

fn parse_test_content(mut content: &str) -> ExpectedTestResult {
   content = content.trim_start();

   let run_anchor = "run:\n";

   let mut expected_compile_output = None;
   if let Some(after_compile) = content.strip_prefix("compile:\n") {
      let mut until_run = after_compile;
      if let Some(start_of_run) = after_compile.rfind(run_anchor) {
         until_run = &until_run[..start_of_run];
         content = &content[start_of_run..];
      }
      expected_compile_output = Some(until_run.to_string());
   }

   let mut expected_run_output = None;
   if let Some(after_run) = content.strip_prefix(run_anchor) {
      expected_run_output = Some(after_run.to_string());
   }

   ExpectedTestResult {
      compile_output: expected_compile_output,
      run_output: expected_run_output,
   }
}
