use std::io::Write;

use crate::interner::Interner;
use crate::source_info::{SourceInfo, SourcePath};

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

   macro_rules! rolandc_warn {
      ($dst:expr, $loc:expr, $($arg:tt)*) => ($dst.emit_warning($loc, format!($($arg)*)))
   }

   pub(crate) use {rolandc_error, rolandc_error_no_loc, rolandc_error_w_details, rolandc_warn};
}

pub enum ErrorLocation {
   Simple(SourceInfo),
   WithDetails(Vec<(SourceInfo, String)>),
   NoLocation,
}

pub struct ErrorInfo {
   pub message: String,
   pub location: ErrorLocation,
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

   pub fn write_out_errors<W: Write>(&self, err_stream: &mut W, interner: &Interner) {
      write_out_error_buf(err_stream, interner, &self.errors);

      if self.errors.is_empty() {
         write_out_error_buf(err_stream, interner, &self.warnings);
      }
   }

   pub fn emit_error(&mut self, location: SourceInfo, message: String) {
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::Simple(location),
      });
   }

   pub fn emit_warning(&mut self, location: SourceInfo, message: String) {
      self.warnings.push(ErrorInfo {
         message,
         location: ErrorLocation::Simple(location),
      });
   }

   pub fn emit_error_with_details<I: ToString>(&mut self, location: &[(SourceInfo, I)], message: String) {
      let location_vec = location.iter().map(|x| (x.0, x.1.to_string())).collect();
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::WithDetails(location_vec),
      });
   }

   pub fn emit_error_no_location(&mut self, message: String) {
      self.errors.push(ErrorInfo {
         message,
         location: ErrorLocation::NoLocation,
      });
   }
}

pub fn write_out_error_buf<W: Write>(err_stream: &mut W, interner: &Interner, buf: &[ErrorInfo]) {
   for error in buf.iter() {
      writeln!(err_stream, "{}", error.message).unwrap();
      match &error.location {
         ErrorLocation::NoLocation => {}
         ErrorLocation::Simple(loc) => {
            emit_source_info(err_stream, *loc, interner);
         }
         ErrorLocation::WithDetails(locs) => {
            for loc in locs {
               emit_source_info_with_description(err_stream, loc.0, &loc.1, interner);
            }
         }
      }
   }
}

pub fn emit_source_info<W: Write>(err_stream: &mut W, source_info: SourceInfo, interner: &Interner) {
   match source_info.file {
      SourcePath::File(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ line {}, column {} [{}]",
            source_info.begin.line + 1,
            source_info.begin.col + 1,
            path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox => {
         writeln!(
            err_stream,
            "↳ line {}, column {}",
            source_info.begin.line + 1,
            source_info.begin.col + 1
         )
         .unwrap();
      }
      SourcePath::Std(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ line {}, column {} [rolandc:{}]",
            source_info.begin.line + 1,
            source_info.begin.col + 1,
            path_str
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
            description,
            source_info.begin.line + 1,
            source_info.begin.col + 1,
            path_str
         )
         .unwrap();
      }
      SourcePath::Std(x) => {
         let path_str = interner.lookup(x);
         writeln!(
            err_stream,
            "↳ {} @ line {}, column {} [rolandc:{}]",
            description,
            source_info.begin.line + 1,
            source_info.begin.col + 1,
            path_str
         )
         .unwrap();
      }
      SourcePath::Sandbox => {
         writeln!(
            err_stream,
            "↳ {} @ line {}, column {}",
            description,
            source_info.begin.line + 1,
            source_info.begin.col + 1
         )
         .unwrap();
      }
   }
}
