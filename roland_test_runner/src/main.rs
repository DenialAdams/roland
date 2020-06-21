use std::env;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Mutex;

use difference::{Changeset, Difference};

use os_pipe::pipe;

use rayon::prelude::*;

use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

enum TestFailureReason {
   ExpectedCompilationFailure,
   ExpectedCompilationSuccess,
   ExpectedCompilationSuccessNoExecutable,
   MismatchedExecutionOutput(Changeset),
   MismatchedCompilationErrorOutput(Changeset),
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
      .filter(|e| e.extension().and_then(OsStr::to_str) == Some("ro"))
      .collect();

   entries.par_iter().for_each(|entry| {
      let tc_output = Command::new(tc_path.clone())
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
            write!(&mut out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap());
            let _ = out_handle.set_color(&pass_color);
            writeln!(&mut out_handle, "ok");
            let _ = out_handle.set_color(&reset_color);
         }
         Err(reason) => {
            lock.1 += 1;
            let stderr = StandardStream::stderr(ColorChoice::Auto);
            let mut out_handle = stderr.lock();
            let _ = out_handle.set_color(&reset_color);
            writeln!(&mut out_handle, "--------------------");
            write!(&mut out_handle, "{}: ", entry.file_name().unwrap().to_str().unwrap());
            let _ = out_handle.set_color(&err_color);
            writeln!(&mut out_handle, "FAILED");
            let _ = out_handle.set_color(&reset_color);
            match reason {
               TestFailureReason::ExpectedCompilationFailure => {
                  writeln!(&mut out_handle, "Compilation was supposed to fail, but it succeeded.");
               }
               TestFailureReason::ExpectedCompilationSuccess => {
                  writeln!(&mut out_handle, "Compilation was supposed to succeed, but it failed:");
                  writeln!(&mut out_handle, "```");
                  writeln!(&mut out_handle, "{}", String::from_utf8_lossy(&tc_output.stderr));
                  writeln!(&mut out_handle, "```");
               }
               TestFailureReason::ExpectedCompilationSuccessNoExecutable => {
                  writeln!(&mut out_handle, "Compilation was supposed to succeed, but no executable was produced and there was no error output from the compiler");
               }
               TestFailureReason::MismatchedExecutionOutput(diff) => {
                  writeln!(
                     &mut out_handle,
                     "Compiled OK, but execution of the program produced a different result than expected:"
                  );
                  writeln!(&mut out_handle, "```");
                  print_diff(&mut out_handle, &diff.diffs);
                  writeln!(&mut out_handle, "```");
               }
               TestFailureReason::MismatchedCompilationErrorOutput(diff) => {
                  writeln!(
                     &mut out_handle,
                     "Failed to compile, but the compilation error was different than expected:"
                  );
                  writeln!(&mut out_handle, "```");
                  print_diff(&mut out_handle, &diff.diffs);
                  writeln!(&mut out_handle, "```");
               }
            }
            writeln!(&mut out_handle, "--------------------");
         }
      }
   });

   let stdout = StandardStream::stdout(ColorChoice::Auto);
   let mut out_handle = stdout.lock();

   let lock = output_mutex.lock().unwrap();

   let _ = out_handle.set_color(&pass_color);
   write!(&mut out_handle, "{} ", lock.0);
   let _ = out_handle.set_color(&reset_color);
   write!(&mut out_handle, "successes, ");
   let _ = out_handle.set_color(&err_color);
   write!(&mut out_handle, "{} ", lock.1);
   let _ = out_handle.set_color(&reset_color);
   writeln!(&mut out_handle, "failures");

   Ok(())
}

fn print_diff<W: WriteColor>(t: &mut W, diffs: &[Difference]) {
   for diff in diffs.iter() {
      match diff {
         Difference::Same(ref x) => {
            let _ = t.set_color(ColorSpec::new().set_fg(None).set_intense(false));
            writeln!(t, "{}", x);
         }
         Difference::Add(ref x) => {
            let _ = t.set_color(ColorSpec::new().set_fg(Some(Color::Green)).set_intense(false));
            writeln!(t, "+{}", x);
         }
         Difference::Rem(ref x) => {
            let _ = t.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_intense(false));
            writeln!(t, "-{}", x);
         }
      }
   }
   let _ = t.set_color(ColorSpec::new().set_fg(None).set_intense(false));
}

fn test_result(tc_output: &Output, t_file_path: &Path, result_dir: &Path) -> Result<(), TestFailureReason> {
   let mut desired_result = String::new();

   if tc_output.stderr.is_empty() {
      let mut prog_path = t_file_path.to_path_buf();
      prog_path.set_extension("");
      let out_file = open_result_file(result_dir, t_file_path, "out");
      if let Ok(mut handle) = out_file {
         handle.read_to_string(&mut desired_result).unwrap();
         let mut prog_output = String::new();
         {
            let mut prog_command = Command::new(prog_path.clone());
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
            let changeset = Changeset::new(&desired_result, &prog_output, "\n");
            return Err(TestFailureReason::MismatchedExecutionOutput(changeset));
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
            let changeset = Changeset::new(&desired_result, &stderr_text, "\n");
            return Err(TestFailureReason::MismatchedCompilationErrorOutput(changeset));
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
