use std::io::Write;

use tempfile::NamedTempFile;

pub type FileAndPath = NamedTempFile;

pub fn get_input_file(bytes: &[u8]) -> Result<FileAndPath, std::io::Error> {
   let mut input = tempfile::NamedTempFile::new()?;
   input.write_all(bytes)?;
   Ok(input)
}

pub fn get_output_file() -> Result<FileAndPath, std::io::Error> {
   let output = tempfile::NamedTempFile::new()?;
   Ok(output)
}
