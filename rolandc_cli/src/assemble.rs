use std::path::Path;
use std::process::Command;

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

pub fn assemble_bytes(bytes: &[u8]) -> Result<FileAndPath, QbeCompilationError> {
   let input = get_input_file(bytes).map_err(QbeCompilationError::AsInvocation)?;

   assemble_file(input.path())
}

pub fn assemble_file(path: &Path) -> Result<FileAndPath, QbeCompilationError> {
   let output = get_output_file().map_err(QbeCompilationError::AsInvocation)?;

   match Command::new("as").arg("-o").arg(output.path()).arg(path).status() {
      Ok(stat) if stat.success() => Ok(output),
      Ok(stat) => Err(QbeCompilationError::AsExecution(stat)),
      Err(e) => Err(QbeCompilationError::AsInvocation(e)),
   }
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
