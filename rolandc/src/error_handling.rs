use std::io::Write;

use crate::interner::Interner;
use crate::lex::{SourceInfo, SourcePath};

pub(crate) mod error_handling_macros {
   macro_rules! rolandc_error {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_error($loc, format!($($arg)*)))
   }

   macro_rules! rolandc_error_no_loc {
      ($dst:expr, $($arg:tt)*) => ($dst.emit_error_no_location(format!($($arg)*)))
   }

   macro_rules! rolandc_error_w_details {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_error_with_details($loc, format!($($arg)*)))
   }

   pub(crate) use {rolandc_error, rolandc_error_no_loc, rolandc_error_w_details};
}

pub enum ErrorLocation {
   Simple(SourceInfo),
   WithDetails(Vec<(SourceInfo, &'static str)>),
   NoLocation,
}

pub struct ErrorInfo {
   pub message: String,
   pub location: ErrorLocation,
}

pub struct ErrorManager {
   pub errors: Vec<ErrorInfo>,
}

impl ErrorManager {
   #[must_use]
   pub fn new() -> ErrorManager {
      ErrorManager { errors: Vec::new() }
   }

   pub fn clear(&mut self) {
      self.errors.clear();
   }

   pub fn write_out_errors<W: Write>(&self, err_stream: &mut W, interner: &Interner) {
      for error in self.errors.iter() {
         writeln!(err_stream, "{}", error.message).unwrap();
         match &error.location {
            ErrorLocation::NoLocation => {}
            ErrorLocation::Simple(loc) => {
               emit_source_info(err_stream, *loc, interner);
            }
            ErrorLocation::WithDetails(locs) => {
               for loc in locs {
                  emit_source_info_with_description(err_stream, loc.0, loc.1, interner);
               }
            }
         }
      }
   }

   pub fn emit_error(&mut self, location: SourceInfo, message: String) {
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::Simple(location),
      });
   }

   pub fn emit_error_with_details(&mut self, location: &[(SourceInfo, &'static str)], message: String) {
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::WithDetails(location.to_vec()),
      });
   }

   pub fn emit_error_no_location(&mut self, message: String) {
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::NoLocation,
      });
   }
}

pub fn emit_source_info<W: Write>(err_stream: &mut W, source_info: SourceInfo, interner: &Interner) {
   match source_info.file {
      SourcePath::File(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ line {}, column {} [{}]",
            source_info.begin.line + 1, source_info.begin.col + 1, path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox | SourcePath::Std => {
         writeln!(
            err_stream,
            "↳ line {}, column {}",
            source_info.begin.line + 1, source_info.begin.col + 1
         )
         .unwrap();
      }
   }
}

pub fn emit_source_info_with_description<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   description: &str,
   interner: &Interner,
) {
   match source_info.file {
      SourcePath::File(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ {} @ line {}, column {} [{}]",
            description, source_info.begin.line + 1, source_info.begin.col + 1, path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox | SourcePath::Std => {
         writeln!(
            err_stream,
            "↳ {} @ line {}, column {}",
            description, source_info.begin.line + 1, source_info.begin.col + 1
         )
         .unwrap();
      }
   }
}
