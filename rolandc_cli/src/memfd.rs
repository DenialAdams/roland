use std::fs::File;
use std::io::{Seek, Write};
use std::os::fd::AsRawFd;
use std::path::{Path, PathBuf};

use nix::sys::memfd::{MFdFlags, memfd_create};

pub struct FileAndPath {
   path: PathBuf,
   handle: File,
}

impl FileAndPath {
   pub fn path(&self) -> &Path {
      &self.path
   }
}

impl std::io::Seek for FileAndPath {
   fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64> {
      self.handle.seek(pos)
   }
}

impl std::io::Read for FileAndPath {
   fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
      self.handle.read(buf)
   }
}

pub fn get_input_file(bytes: &[u8]) -> Result<FileAndPath, std::io::Error> {
   let input_fd = memfd_create("", MFdFlags::empty())?;
   let mut input = File::from(input_fd);
   input.write_all(bytes)?;
   Ok(if cfg!(target_os = "linux") {
      FileAndPath {
         path: PathBuf::from(format!("/proc/self/fd/{}", input.as_raw_fd())),
         handle: input,
      }
   } else {
      input.rewind()?;
      FileAndPath {
         path: PathBuf::from(format!("/dev/fd/{}", input.as_raw_fd())),
         handle: input,
      }
   })
}

pub fn get_output_file() -> Result<FileAndPath, std::io::Error> {
   let output_fd = memfd_create("", MFdFlags::empty())?;
   let output = File::from(output_fd);
   Ok(if cfg!(target_os = "linux") {
      FileAndPath {
         path: PathBuf::from(format!("/proc/self/fd/{}", output.as_raw_fd())),
         handle: output,
      }
   } else {
      FileAndPath {
         path: PathBuf::from(format!("/dev/fd/{}", output.as_raw_fd())),
         handle: output,
      }
   })
}
