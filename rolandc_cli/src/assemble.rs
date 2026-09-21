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
   use std::process::Command;

   use crate::QbeCompilationError;

   let input = get_input_file(bytes).map_err(QbeCompilationError::AsInvocation)?;

   let output = get_output_file().map_err(QbeCompilationError::AsInvocation)?;

   match Command::new("as")
      .arg("-o")
      .arg(output.path())
      .arg(input.path())
      .status()
   {
      Ok(stat) if stat.success() => Ok(output),
      Ok(stat) => Err(QbeCompilationError::AsExecution(stat)),
      Err(e) => Err(QbeCompilationError::AsInvocation(e)),
   }
}
