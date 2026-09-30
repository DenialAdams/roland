use std::path::Path;
use std::process::{Child, Command};

use crate::QbeCompilationError;

#[cfg_attr(any(target_os = "linux", target_os = "freebsd"), path = "memfd.rs")]
#[cfg_attr(not(any(target_os = "linux", target_os = "freebsd")), path = "tempfile.rs")]
mod imp;

fn get_input_file(bytes: &[u8]) -> Result<imp::FileAndPath, std::io::Error> {
   imp::get_input_file(bytes)
}

fn get_output_file() -> Result<imp::FileAndPath, std::io::Error> {
   imp::get_output_file()
}

type FileAndPath = imp::FileAndPath;

pub struct PendingAssemblyInvocation {
   child: Child,
   output: FileAndPath,
   input: Option<FileAndPath>,
}

impl PendingAssemblyInvocation {
   pub fn wait(mut self) -> Result<FileAndPath, QbeCompilationError> {
      match self.child.wait() {
         Ok(stat) if stat.success() => Ok(self.output),
         Ok(stat) => Err(QbeCompilationError::AsExecution(stat)),
         Err(e) => Err(QbeCompilationError::AsInvocation(e)),
      }
   }
}

pub fn assemble_bytes(bytes: &[u8]) -> Result<PendingAssemblyInvocation, QbeCompilationError> {
   let input = get_input_file(bytes).map_err(QbeCompilationError::AsInvocation)?;

   let mut pending = assemble_file(input.path())?;
   pending.input = Some(input);
   Ok(pending)
}

pub fn assemble_file(path: &Path) -> Result<PendingAssemblyInvocation, QbeCompilationError> {
   let output = get_output_file().map_err(QbeCompilationError::AsInvocation)?;

   let child = Command::new("as")
      .arg("-o")
      .arg(output.path())
      .arg(path)
      .spawn()
      .map_err(QbeCompilationError::AsInvocation)?;

   Ok(PendingAssemblyInvocation {
      child,
      output,
      input: None,
   })
}

pub fn invoke_qbe(program_bytes: &[u8]) -> Result<FileAndPath, QbeCompilationError> {
   let mut qbe_command = if let Some(extant_local_qbe) = std::env::current_exe()
      .ok()
      .map(|mut x| {
         x.set_file_name("qbe");
         x
      })
      .filter(|x| x.exists())
   {
      Command::new(extant_local_qbe)
   } else {
      Command::new("qbe")
   };

   let input = get_input_file(program_bytes).map_err(QbeCompilationError::QbeInvocation)?;
   let output = get_output_file().map_err(QbeCompilationError::QbeInvocation)?;

   match qbe_command.arg("-o").arg(output.path()).arg(input.path()).status() {
      Ok(stat) if stat.success() => Ok(output),
      Ok(stat) => Err(QbeCompilationError::QbeExecution(stat)),
      Err(e) => Err(QbeCompilationError::QbeInvocation(e)),
   }
}
