#![allow(clippy::uninlined_format_args)] // I'm an old man and I like the way it was before
#![allow(clippy::unwrap_or_default)] // I want to know exactly what is being called

use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use os_pipe::pipe;
use rayon::prelude::*;
use similar_asserts::SimpleDiff;
use wait_timeout::ChildExt;

enum TestFailureReason {
   TestingNothing(String, File),
   ExpectedCompilationSuccess(String),
   FailedToRunExecutable,
   MismatchedExecutionOutput(String, String),
   MismatchedCompilationErrorOutput(String, TestDetails),
   ExecutionTimeout,
}

struct Opts {
   test_path: PathBuf,
   tc_path: PathBuf,
   overwrite_error_files: bool,
   amd64: bool,
   preserve_artifacts: bool,
}

fn parse_path(s: &std::ffi::OsStr) -> Result<std::path::PathBuf, &'static str> {
   Ok(s.into())
}

fn parse_args() -> Result<Opts, pico_args::Error> {
   let mut pargs = pico_args::Arguments::from_env();

   let cli_path = pargs.value_from_os_str("--cli", parse_path)?;

   let opts = Opts {
      test_path: pargs.free_from_os_str(parse_path)?,
      tc_path: cli_path,
      overwrite_error_files: pargs.contains("--overwrite-error-files"),
      amd64: pargs.contains("--amd64"),
      preserve_artifacts: pargs.contains("--preserve-artifacts"),
   };

   let remaining_args = pargs.finish();

   if !remaining_args.is_empty() {
      let remaining_args_unicode: Vec<_> = remaining_args.iter().map(|x| x.to_string_lossy()).collect();
      eprintln!("Unrecognized arguments: '{}'", remaining_args_unicode.join("', '"));
      std::process::exit(1);
   }

   Ok(opts)
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
   let failures = Mutex::new(Vec::new());
   let output_lock = Mutex::new(());

   entries.par_iter().for_each(|entry| {
      let tc_output = if opts.amd64 {
         Command::new(&opts.tc_path)
            .arg(entry.clone())
            .arg("--amd64")
            .arg("--output")
            .arg({
               let mut x = entry.clone();
               x.set_extension("out");
               x
            })
            .output()
            .unwrap()
      } else {
         Command::new(&opts.tc_path).arg(entry.clone()).output().unwrap()
      };
      let test_ok = test_result(&tc_output, entry, opts.amd64, opts.preserve_artifacts);
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
            failures
               .lock()
               .unwrap()
               .push((entry.file_name().unwrap().to_str().unwrap(), reason));
         }
      }
   });

   let mut failures = failures.into_inner().unwrap();

   for (name, ref mut reason) in failures.iter_mut() {
      let mut out_handle = std::io::stderr().lock();
      color_reset(&mut out_handle).unwrap();
      writeln!(out_handle, "--------------------").unwrap();
      write!(out_handle, "{}: ", name).unwrap();
      bold_red(&mut out_handle).unwrap();
      writeln!(out_handle, "FAILED").unwrap();
      color_reset(&mut out_handle).unwrap();
      match reason {
         TestFailureReason::TestingNothing(actual, ref mut file) => {
            if !opts.overwrite_error_files {
               writeln!(out_handle, "There was no test specified for this input.").unwrap();
            }

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
         TestFailureReason::ExpectedCompilationSuccess(err_out) => {
            writeln!(out_handle, "Compilation was supposed to succeed, but it failed:").unwrap();
            writeln!(out_handle, "```").unwrap();
            writeln!(out_handle, "{}", err_out).unwrap();
            writeln!(out_handle, "```").unwrap();
         }
         TestFailureReason::FailedToRunExecutable => {
            writeln!(
               out_handle,
               "Compilation seemingly succeeded, but the executable failed to run. Is wasmtime installed?"
            )
            .unwrap();
         }
         TestFailureReason::ExecutionTimeout => {
            writeln!(out_handle, "Compiled OK, but the executable failed to terminate.").unwrap();
         }
         TestFailureReason::MismatchedExecutionOutput(expected, actual) => {
            writeln!(
               out_handle,
               "Compiled OK, but execution of the program produced a different result than expected:"
            )
            .unwrap();
            print_diff(&mut out_handle, expected, actual);
         }
         TestFailureReason::MismatchedCompilationErrorOutput(actual, ref mut test_details) => {
            if opts.overwrite_error_files {
               // file should have been sunk to the correct point
               test_details.file.write_all(b"compile:\n").unwrap();
               test_details.file.write_all(actual.as_bytes()).unwrap();
               if let Some(r) = test_details.result.run_output.as_ref() {
                  test_details.file.write_all(b"\nrun:\n").unwrap();
                  test_details.file.write_all(r.as_bytes()).unwrap();
               }
               let current_position = test_details.file.stream_position().unwrap();
               test_details.file.set_len(current_position).unwrap();
               print_diff(
                  &mut out_handle,
                  test_details.result.compile_output.as_ref().map_or("", |x| x.as_str()),
                  actual,
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
                  actual,
               );
            }
         }
      }
      writeln!(out_handle, "--------------------").unwrap();
   }

   let num_successes = successes.load(Ordering::Relaxed);
   let num_failures = failures.len();

   let mut out_handle = std::io::stdout().lock();

   bold_green(&mut out_handle).unwrap();
   write!(out_handle, "{} ", num_successes).unwrap();
   color_reset(&mut out_handle).unwrap();
   if num_successes == 1 {
      write!(out_handle, "success, ").unwrap();
   } else {
      write!(out_handle, "successes, ").unwrap();
   }
   bold_red(&mut out_handle).unwrap();
   write!(out_handle, "{} ", num_failures).unwrap();
   color_reset(&mut out_handle).unwrap();
   if num_failures == 1 {
      writeln!(out_handle, "failure").unwrap();
   } else {
      writeln!(out_handle, "failures").unwrap();
   }
   Ok(())
}

fn print_diff<W: Write>(t: &mut W, expected: &str, actual: &str) {
   writeln!(t, "{}", SimpleDiff::from_str(expected, actual, "expected", "actual")).unwrap();
}

fn test_result(
   tc_output: &Output,
   t_file_path: &Path,
   amd64: bool,
   preserve_artifacts: bool,
) -> Result<(), TestFailureReason> {
   let td = extract_test_data(t_file_path, amd64);

   let stderr_text = String::from_utf8_lossy(&tc_output.stderr);

   if td.result.compile_output.is_none() && td.result.run_output.is_none() {
      return Err(TestFailureReason::TestingNothing(stderr_text.into_owned(), td.file));
   }

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
      if amd64 {
         prog_path.set_extension("out");
      } else {
         prog_path.set_extension("wasm");
      }

      let prog_output = {
         let (mut handle, mut prog_output_stream) = {
            let mut prog_command = if amd64 {
               Command::new(&prog_path)
            } else {
               let mut prog_command = Command::new("wasmtime");
               prog_command.arg(prog_path.as_os_str());
               prog_command
            };
            // It's desirable to combine stdout and stderr, so an output test can test either or both
            let prog_output_stream = {
               let (reader, writer) = pipe().unwrap();
               let writer_clone = writer.try_clone().unwrap();
               prog_command.stdout(writer);
               prog_command.stderr(writer_clone);
               reader
            };
            let handle = match prog_command.spawn() {
               Ok(v) => v,
               Err(_) => {
                  return Err(TestFailureReason::FailedToRunExecutable);
               }
            };
            (handle, prog_output_stream)
         };
         match handle.wait_timeout(Duration::from_secs(1)).unwrap() {
            Some(_status) => (),
            None => {
               handle.kill().unwrap();
               return Err(TestFailureReason::ExecutionTimeout);
            }
         };
         let mut prog_output: Vec<u8> = Vec::new();
         prog_output_stream.read_to_end(&mut prog_output).unwrap();
         String::from_utf8_lossy(&prog_output).into_owned()
      };

      if prog_output != ero {
         return Err(TestFailureReason::MismatchedExecutionOutput(ero, prog_output));
      }

      if preserve_artifacts && !amd64 {
         let mut out_path = prog_path.clone();
         out_path.set_extension("wat");
         let mut prog_command = Command::new("wasm2wat");
         prog_command.arg("-o");
         prog_command.arg(out_path.as_os_str());
         prog_command.arg(prog_path.as_os_str());
         prog_command.status().unwrap();
      }

      std::fs::remove_file(&prog_path).unwrap();

      if amd64 && !preserve_artifacts {
         prog_path.set_extension("s");
         std::fs::remove_file(&prog_path).unwrap();
         prog_path.set_extension("ssa");
         std::fs::remove_file(&prog_path).unwrap();
      }
   } else if td.result.run_output.is_some() {
      return Err(TestFailureReason::ExpectedCompilationSuccess(stderr_text.into_owned()));
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

fn extract_test_data(entry: &Path, amd64: bool) -> TestDetails {
   let mut opened = OpenOptions::new().read(true).write(true).open(entry).unwrap();

   let mut s = String::new();
   opened.read_to_string(&mut s).unwrap();

   let anchor = "__END__\n";
   let anchor_location = s.rfind(anchor);
   let test_output = if let Some(loc) = anchor_location {
      opened.seek(SeekFrom::Start((loc + anchor.len()) as u64)).unwrap();
      parse_test_content(&s[loc + anchor.len()..], amd64)
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
      parse_test_content(&s, amd64)
   };

   TestDetails {
      file: opened,
      result: test_output,
   }
}

fn parse_test_content(mut content: &str, amd64: bool) -> ExpectedTestResult {
   content = content.trim_start();

   #[derive(Copy, Clone)]
   enum TargetSpec {
      Amd64,
      Wasi,
      Generic,
   }

   let anchors = [
      (b"compile_amd64:\n".as_slice(), TargetSpec::Amd64, true),
      (b"compile_wasi:\n".as_slice(), TargetSpec::Wasi, true),
      (b"compile:\n".as_slice(), TargetSpec::Generic, true),
      (b"run_amd64:\n".as_slice(), TargetSpec::Amd64, false),
      (b"run_wasi:\n".as_slice(), TargetSpec::Wasi, false),
      (b"run:\n".as_slice(), TargetSpec::Generic, false),
   ];

   let mut expected_compile_output: Option<Vec<u8>> = None;
   let mut expected_run_output: Option<Vec<u8>> = None;

   // Possible contents:
   // compile: followed by run:
   // run:
   // compile:
   // compile and run can optionally be suffixed by a target
   // i.e. compile_amd64, run_amd64, compile_wasi, run_wasi
   // in which case we can have multiple compile tokens

   enum Mode<'a> {
      ExpectingAnchor,
      ParsingAnchor(&'a mut Vec<u8>),
   }

   let mut mode = Mode::ExpectingAnchor;
   let mut content_view = content.as_bytes();

   'outer: while !content_view.is_empty() {
      for anchor in anchors.iter() {
         if content_view.starts_with(anchor.0) {
            content_view = &content_view[anchor.0.len()..];
            match (amd64, anchor.1) {
               (true, TargetSpec::Wasi) | (false, TargetSpec::Amd64) => {
                  mode = Mode::ExpectingAnchor;
               }
               _ => {
                  if anchor.2 {
                     expected_compile_output = Some(Vec::new());
                     mode = Mode::ParsingAnchor(expected_compile_output.as_mut().unwrap());
                  } else {
                     expected_run_output = Some(Vec::new());
                     mode = Mode::ParsingAnchor(expected_run_output.as_mut().unwrap());
                  }
               }
            }
            continue 'outer;
         }
      }
      match mode {
         Mode::ExpectingAnchor => (),
         Mode::ParsingAnchor(ref mut buf) => {
            buf.push(content_view[0]);
         }
      }
      content_view = &content_view[1..];
   }

   ExpectedTestResult {
      compile_output: expected_compile_output.map(|x| String::from_utf8(x).unwrap()),
      run_output: expected_run_output.map(|x| String::from_utf8(x).unwrap()),
   }
}
