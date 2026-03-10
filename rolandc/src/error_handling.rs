use std::borrow::Cow;
use std::io::Write;
use std::{env, fmt};

use indexmap::IndexSet;

use crate::FileMap;
use crate::source_info::SourceInfo;

pub(crate) mod error_handling_macros {
   macro_rules! rolandc_error {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_error($loc, format_args!($($arg)*)))
   }

   macro_rules! rolandc_error_no_loc {
      ($dst:expr, $($arg:tt)*) => ($dst.emit_error_no_location(format_args!($($arg)*)))
   }

   macro_rules! rolandc_error_w_details {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_error_with_details($loc, format_args!($($arg)*)))
   }

   macro_rules! rolandc_warn {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_warning($loc, format_args!($($arg)*)))
   }

   pub(crate) use rolandc_error;
   pub(crate) use rolandc_error_no_loc;
   pub(crate) use rolandc_error_w_details;
   pub(crate) use rolandc_warn;
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum ErrorLocation {
   Simple(SourceInfo),
   WithDetails(Vec<(SourceInfo, String)>),
   NoLocation,
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub struct ErrorInfo {
   pub message: String,
   pub location: ErrorLocation,
   pub came_from_stack: Vec<SourceInfo>,
}

pub struct ErrorManager {
   pub errors: Vec<ErrorInfo>,
   pub warnings: Vec<ErrorInfo>,
}

impl ErrorManager {
   #[must_use]
   pub fn new() -> ErrorManager {
      ErrorManager {
         errors: Vec::new(),
         warnings: Vec::new(),
      }
   }

   pub fn clear(&mut self) {
      self.errors.clear();
      self.warnings.clear();
   }

   pub fn write_out_errors<W: Write>(&self, err_stream: &mut W, show_file_paths: bool, user_files: &FileMap) {
      let errs_unique: IndexSet<ErrorInfo> = self.errors.iter().cloned().collect();
      write_out_error_buf(err_stream, errs_unique.iter(), show_file_paths, user_files);

      if self.errors.is_empty() {
         let warns_unique: IndexSet<ErrorInfo> = self.warnings.iter().cloned().collect();
         write_out_error_buf(err_stream, warns_unique.iter(), show_file_paths, user_files);
      }
   }

   pub fn emit_error(&mut self, location: SourceInfo, message: fmt::Arguments) {
      self.errors.push(ErrorInfo {
         message: message.to_string(),
         location: ErrorLocation::Simple(location),
         came_from_stack: Vec::new(),
      });
   }

   pub fn emit_warning(&mut self, location: SourceInfo, message: fmt::Arguments) {
      self.warnings.push(ErrorInfo {
         message: message.to_string(),
         location: ErrorLocation::Simple(location),
         came_from_stack: Vec::new(),
      });
   }

   pub fn emit_error_with_details<I: ToString>(&mut self, location: &[(SourceInfo, I)], message: fmt::Arguments) {
      let location_vec = location.iter().map(|x| (x.0, x.1.to_string())).collect();
      self.errors.push(ErrorInfo {
         message: message.to_string(),
         location: ErrorLocation::WithDetails(location_vec),
         came_from_stack: Vec::new(),
      });
   }

   pub fn emit_error_no_location(&mut self, message: fmt::Arguments) {
      self.errors.push(ErrorInfo {
         message: message.to_string(),
         location: ErrorLocation::NoLocation,
         came_from_stack: Vec::new(),
      });
   }
}

pub fn write_out_error_buf<'a, W: Write, I: IntoIterator<Item = &'a ErrorInfo>>(
   err_stream: &mut W,
   buf: I,
   show_file_paths: bool,
   user_files: &FileMap,
) {
   // Error paths refer to canonical paths - i.e. fully expanded, symlinks resolved, etc.
   // In an attempt to make the errors more concise, we remove the prefix
   // n.b. it's weird that we use the current working directory for this purpose -
   // would be better for clients to pass it in, since this is library code.
   // Possibly good enough for now.
   let canonical_cwd = env::current_dir().and_then(std::fs::canonicalize);
   let cwd_str = canonical_cwd
      .as_ref()
      .map_or(Cow::Borrowed(""), |x| x.to_string_lossy());
   for error in buf {
      writeln!(err_stream, "{}", error.message).unwrap();
      match &error.location {
         ErrorLocation::NoLocation => {}
         ErrorLocation::Simple(loc) => {
            emit_source_info(err_stream, *loc, &cwd_str, show_file_paths, user_files);
         }
         ErrorLocation::WithDetails(locs) => {
            for (loc, label) in locs {
               emit_source_info_with_description(err_stream, *loc, label, &cwd_str, show_file_paths, user_files);
            }
         }
      }
      for source in error.came_from_stack.iter().copied() {
         emit_source_info_with_description(err_stream, source, "instantiation", &cwd_str, show_file_paths, user_files);
      }
   }
}

fn emit_source_info<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   base_dir: &str,
   show_file_paths: bool,
   user_files: &FileMap,
) {
   let ((path, is_std), _file_contents) = user_files.get_index(source_info.file.0).unwrap();

   if *is_std {
      let path_str = path.to_string_lossy();
      writeln!(
         err_stream,
         "↳ line {}, column {} [rolandc:{}]",
         source_info.begin.line + 1,
         source_info.begin.col + 1,
         path_str
      )
      .unwrap();
   } else if show_file_paths {
      let path_str = path.strip_prefix(base_dir).unwrap_or(path).to_string_lossy();
      writeln!(
         err_stream,
         "↳ line {}, column {} [{}]",
         source_info.begin.line + 1,
         source_info.begin.col + 1,
         path_str
      )
      .unwrap();
   } else {
      writeln!(
         err_stream,
         "↳ line {}, column {}",
         source_info.begin.line + 1,
         source_info.begin.col + 1,
      )
      .unwrap();
   }
}

fn emit_source_info_with_description<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   description: &str,
   base_dir: &str,
   show_file_paths: bool,
   user_files: &FileMap,
) {
   let ((path, is_std), _file_contents) = user_files.get_index(source_info.file.0).unwrap();

   if *is_std {
      let path_str = path.to_string_lossy();
      writeln!(
         err_stream,
         "↳ {} @ line {}, column {} [rolandc:{}]",
         description,
         source_info.begin.line + 1,
         source_info.begin.col + 1,
         path_str
      )
      .unwrap();
   } else if show_file_paths {
      let path_str = path.strip_prefix(base_dir).unwrap_or(path).to_string_lossy();
      writeln!(
         err_stream,
         "↳ {} @ line {}, column {} [{}]",
         description,
         source_info.begin.line + 1,
         source_info.begin.col + 1,
         path_str,
      )
      .unwrap();
   } else {
      writeln!(
         err_stream,
         "↳ {} @ line {}, column {}",
         description,
         source_info.begin.line + 1,
         source_info.begin.col + 1,
      )
      .unwrap();
   }
}
