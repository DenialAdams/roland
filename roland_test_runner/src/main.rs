use std::env;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Mutex;

use similar::text::{ChangeTag, TextDiff};

use os_pipe::pipe;

use rayon::prelude::*;

use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

enum TestFailureReason {
   ExpectedCompilationFailure,
   ExpectedCompilationSuccess,
   ExpectedCompilationSuccessNoExecutable,
   MismatchedExecutionOutput(String, String),
   MismatchedCompilationErrorOutput(String, String),
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

   let (test_path, tc_path) = {
      let mut args = env::args();
      if args.len() != 3 {
         return Err("Expected exactly 2 arguments");
      }
      (PathBuf::from(args.nth(1).unwrap()), args.next().unwrap())
   };

   env::set_current_dir(test_path).unwrap();

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
      let tc_output = Command::new(tc_path.as_str())
         .arg("-o")
         .arg(entry.file_stem().unwrap())
         .arg(entry.file_name().unwrap())
         .output()
         .unwrap();
      let test_ok = test_result(&tc_output, &entry, &result_dir);
      let mut lock = output_mutex.lock().unwrap();
      match test_ok {
         Ok(()) => {
            lock.0 += 1;
            let stdout = StandardStream::stdout(ColorChoice::Auto);
            let mut out_handle = stdout.lock();
            let _ = out_handle.set_color(&reset_color);
            write!(&mut out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            let _ = out_handle.set_color(&pass_color);
            writeln!(&mut out_handle, "ok").unwrap();
            let _ = out_handle.set_color(&reset_color);
         }
         Err(reason) => {
            lock.1 += 1;
            let stderr = StandardStream::stderr(ColorChoice::Auto);
            let mut out_handle = stderr.lock();
            let _ = out_handle.set_color(&reset_color);
            writeln!(&mut out_handle, "--------------------").unwrap();
            write!(&mut out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap()).unwrap();
            let _ = out_handle.set_color(&err_color);
            writeln!(&mut out_handle, "FAILED").unwrap();
            let _ = out_handle.set_color(&reset_color);
            match reason {
               TestFailureReason::ExpectedCompilationFailure => {
                  writeln!(&mut out_handle, "Compilation was supposed to fail, but it succeeded.").unwrap();
               }
               TestFailureReason::ExpectedCompilationSuccess => {
                  writeln!(&mut out_handle, "Compilation was supposed to succeed, but it failed:").unwrap();
                  writeln!(&mut out_handle, "```").unwrap();
                  writeln!(&mut out_handle, "{}", String::from_utf8_lossy(&tc_output.stderr)).unwrap();
                  writeln!(&mut out_handle, "```").unwrap();
               }
               TestFailureReason::ExpectedCompilationSuccessNoExecutable => {
                  writeln!(&mut out_handle, "Compilation was supposed to succeed, but no executable was produced and there was no error output from the compiler").unwrap();
               }
               TestFailureReason::MismatchedExecutionOutput(expected, actual) => {
                  writeln!(
                     &mut out_handle,
                     "Compiled OK, but execution of the program produced a different result than expected:"
                  ).unwrap();
                  print_diff(&mut out_handle, &expected, &actual);
               }
               TestFailureReason::MismatchedCompilationErrorOutput(expected, actual) => {
                  writeln!(
                     &mut out_handle,
                     "Failed to compile, but the compilation error was different than expected:"
                  ).unwrap();
                  print_diff(&mut out_handle, &expected, &actual);
               }
            }
            writeln!(&mut out_handle, "--------------------").unwrap();
         }
      }
   });

   let stdout = StandardStream::stdout(ColorChoice::Auto);
   let mut out_handle = stdout.lock();

   let lock = output_mutex.lock().unwrap();

   let _ = out_handle.set_color(&pass_color);
   write!(&mut out_handle, "{} ", lock.0).unwrap();
   let _ = out_handle.set_color(&reset_color);
   if lock.0 == 1 {
      write!(&mut out_handle, "success, ").unwrap();
   } else {
      write!(&mut out_handle, "successes, ").unwrap();
   }
   let _ = out_handle.set_color(&err_color);
   write!(&mut out_handle, "{} ", lock.1).unwrap();
   let _ = out_handle.set_color(&reset_color);
   if lock.1 == 1 {
      writeln!(&mut out_handle, "failure").unwrap();
   } else {
      writeln!(&mut out_handle, "failures").unwrap();
   }
   Ok(())
}

fn print_diff<W: WriteColor>(t: &mut W, expected: &str, actual: &str) {
   let diff = TextDiff::from_lines(expected, actual);
   let ops = diff.ops();

   writeln!(t, "```").unwrap();
   for op in ops {
      for change in diff.iter_changes(op) {
         match change.tag() {
            ChangeTag::Equal => {
               let _ = t.set_color(ColorSpec::new().set_fg(None).set_intense(false));
               write!(t, "{}", change.value()).unwrap();
            }
            ChangeTag::Insert => {
               let _ = t.set_color(ColorSpec::new().set_fg(Some(Color::Green)).set_intense(false));
               write!(t, "+{}", change.value()).unwrap();
            }
            ChangeTag::Delete => {
               let _ = t.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_intense(false));
               write!(t, "-{}", change.value()).unwrap();
            }
         }
      }
   }
   let _ = t.set_color(ColorSpec::new().set_fg(None).set_intense(false));
   writeln!(t, "```").unwrap();
}

fn test_result(tc_output: &Output, t_file_path: &Path, result_dir: &Path) -> Result<(), TestFailureReason> {
   let mut desired_result = String::new();

   if tc_output.stderr.is_empty() {
      let mut prog_path = t_file_path.to_path_buf();
      prog_path.set_extension("wast");
      let out_file = open_result_file(result_dir, t_file_path, "out");
      if let Ok(mut handle) = out_file {
         handle.read_to_string(&mut desired_result).unwrap();
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
                  return Err(TestFailureReason::ExpectedCompilationSuccessNoExecutable);
               }
            };
            drop(prog_command);
            prog_output_stream.read_to_string(&mut prog_output).unwrap();
            handle.wait().unwrap();
         };
         if prog_output != desired_result {
            return Err(TestFailureReason::MismatchedExecutionOutput(desired_result, prog_output));
         }
      } else {
         return Err(TestFailureReason::ExpectedCompilationFailure);
      }
      std::fs::remove_file(prog_path).unwrap();
   } else {
      let err_file = open_result_file(result_dir, t_file_path, "err");
      if let Ok(mut handle) = err_file {
         handle.read_to_string(&mut desired_result).unwrap();
         let stderr_text = String::from_utf8_lossy(&tc_output.stderr);
         if stderr_text != desired_result {
            return Err(TestFailureReason::MismatchedCompilationErrorOutput(desired_result, stderr_text.into_owned()));
         }
      } else {
         return Err(TestFailureReason::ExpectedCompilationSuccess);
      }
   }

   Ok(())
}

fn open_result_file(result_dir: &Path, entry: &Path, extension: &'static str) -> io::Result<File> {
   let mut out_name = entry.to_path_buf();
   out_name.set_extension(extension);
   let mut out_path = result_dir.to_path_buf();
   out_path.push(out_name.file_name().unwrap());
   File::open(out_path)
}
