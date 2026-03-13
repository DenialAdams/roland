use std::borrow::Cow;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::io::Write;
use std::{env, fmt};

use indexmap::IndexSet;

use crate::FileMap;
use crate::source_info::{SourceInfo, SourcePath};

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

   #[must_use]
   pub fn map_all_err_locations_to_line_col<const COLUMN_IS_CHARS: bool, const INCLUDE_END_LOCATIONS: bool>(
      &self,
      user_files: &FileMap,
   ) -> HashMap<(SourcePath, usize), ExpandedErrorLocation> {
      let mut all_source_locations_by_path: HashMap<SourcePath, Vec<usize>> = HashMap::new();
      for err_info in self.errors.iter().chain(self.warnings.iter()) {
         fn push_si<const INCLUDE_END_LOCATIONS: bool>(map: &mut HashMap<SourcePath, Vec<usize>>, si: &SourceInfo) {
            let v = map.entry(si.file).or_default();
            v.push(si.begin.0);
            if INCLUDE_END_LOCATIONS {
               v.push(si.end.0);
            }
         }
         match &err_info.location {
            ErrorLocation::Simple(si) => {
               push_si::<INCLUDE_END_LOCATIONS>(&mut all_source_locations_by_path, si);
            }
            ErrorLocation::WithDetails(items) => {
               for si in items.iter().map(|x| &x.0) {
                  push_si::<INCLUDE_END_LOCATIONS>(&mut all_source_locations_by_path, si);
               }
            }
            ErrorLocation::NoLocation => (),
         }
         for si in err_info.came_from_stack.iter() {
            push_si::<INCLUDE_END_LOCATIONS>(&mut all_source_locations_by_path, si);
         }
      }
      for val in all_source_locations_by_path.values_mut() {
         val.sort_unstable_by_key(|k| std::cmp::Reverse(*k));
      }

      let mut res: HashMap<(SourcePath, usize), ExpandedErrorLocation> = HashMap::new();
      for (k, v) in all_source_locations_by_path.drain() {
         convert_positions_to_line_column::<COLUMN_IS_CHARS, _>(v, k, user_files.get_index(k.0).unwrap().1, &mut res);
      }

      res
   }

   pub fn write_out_errors<W: Write>(&self, err_stream: &mut W, show_file_paths: bool, user_files: &FileMap) {
      let res = self.map_all_err_locations_to_line_col::<true, false>(user_files);

      let errs_unique: IndexSet<ErrorInfo> = self.errors.iter().cloned().collect();
      write_out_error_buf(err_stream, errs_unique.iter(), show_file_paths, user_files, &res);

      if self.errors.is_empty() {
         let warns_unique: IndexSet<ErrorInfo> = self.warnings.iter().cloned().collect();
         write_out_error_buf(err_stream, warns_unique.iter(), show_file_paths, user_files, &res);
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

pub type ExpandedErrorLocation = (usize, usize);

pub fn convert_positions_to_line_column<const COLUMN_IS_CHARS: bool, S: BuildHasher>(
   mut indices: Vec<usize>,
   path: SourcePath,
   file_contents: &str,
   out_error_locations: &mut HashMap<(SourcePath, usize), ExpandedErrorLocation, S>,
) {
   // There is a potential slowness here, which is that we compute the length in chars for every index
   // which involves scanning the whole line. This isn't necessary, we could compute it incrementally
   // but I think super long lines are sufficiently rare that for now I prefer simplicity -- rjm

   debug_assert!(indices.is_sorted_by_key(std::cmp::Reverse));
   let file_bytes = file_contents.as_bytes();
   out_error_locations.reserve(indices.len());
   let mut current_index: usize = 0;
   let mut current_line: usize = 0;
   'outer: while let Some(next_newline) = memchr::memchr(b'\n', &file_bytes[current_index..]) {
      let end_of_line = current_index + next_newline;
      while let Some(next_index_to_convert) = indices.last().copied() {
         if next_index_to_convert > end_of_line {
            current_index += next_newline + 1;
            current_line += 1;
            continue 'outer;
         }
         let _ = indices.pop();
         debug_assert!(file_contents.is_char_boundary(next_index_to_convert));
         let col = if COLUMN_IS_CHARS {
            file_contents[current_index..next_index_to_convert].chars().count()
         } else {
            next_index_to_convert - current_index
         };
         out_error_locations.insert((path, next_index_to_convert), (current_line, col));
      }
      return;
   }
   while let Some(next_index_to_convert) = indices.pop() {
      debug_assert!(file_contents.is_char_boundary(next_index_to_convert));
      let col = if COLUMN_IS_CHARS {
         file_contents[current_index..next_index_to_convert].chars().count()
      } else {
         next_index_to_convert - current_index
      };
      out_error_locations.insert((path, next_index_to_convert), (current_line, col));
   }
}

fn write_out_error_buf<'a, 'b, W: Write, I: IntoIterator<Item = &'a ErrorInfo>>(
   err_stream: &mut W,
   buf: I,
   show_file_paths: bool,
   user_files: &FileMap,
   expanded_err_map: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
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
            emit_source_info(
               err_stream,
               *loc,
               &cwd_str,
               show_file_paths,
               user_files,
               expanded_err_map,
            );
         }
         ErrorLocation::WithDetails(locs) => {
            for (loc, label) in locs {
               emit_source_info_with_description(
                  err_stream,
                  *loc,
                  label,
                  &cwd_str,
                  show_file_paths,
                  user_files,
                  expanded_err_map,
               );
            }
         }
      }
      for source in error.came_from_stack.iter().copied() {
         emit_source_info_with_description(
            err_stream,
            source,
            "instantiation",
            &cwd_str,
            show_file_paths,
            user_files,
            expanded_err_map,
         );
      }
   }
}

fn emit_source_info<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   base_dir: &str,
   show_file_paths: bool,
   user_files: &FileMap,
   expanded_err_map: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
) {
   let ((path, is_std), _file_contents) = user_files.get_index(source_info.file.0).unwrap();
   let (line, col) = expanded_err_map[&(source_info.file, source_info.begin.0)];

   if *is_std {
      let path_str = path.to_string_lossy();
      writeln!(
         err_stream,
         "↳ line {}, column {} [rolandc:{}]",
         line + 1,
         col + 1,
         path_str
      )
      .unwrap();
   } else if show_file_paths {
      let path_str = path.strip_prefix(base_dir).unwrap_or(path).to_string_lossy();
      writeln!(err_stream, "↳ line {}, column {} [{}]", line + 1, col + 1, path_str).unwrap();
   } else {
      writeln!(err_stream, "↳ line {}, column {}", line + 1, col + 1).unwrap();
   }
}

fn emit_source_info_with_description<W: Write>(
   err_stream: &mut W,
   source_info: SourceInfo,
   description: &str,
   base_dir: &str,
   show_file_paths: bool,
   user_files: &FileMap,
   expanded_err_map: &HashMap<(SourcePath, usize), ExpandedErrorLocation>,
) {
   let ((path, is_std), _file_contents) = user_files.get_index(source_info.file.0).unwrap();
   let (line, col) = expanded_err_map[&(source_info.file, source_info.begin.0)];

   if *is_std {
      let path_str = path.to_string_lossy();
      writeln!(
         err_stream,
         "↳ {} @ line {}, column {} [rolandc:{}]",
         description,
         line + 1,
         col + 1,
         path_str
      )
      .unwrap();
   } else if show_file_paths {
      let path_str = path.strip_prefix(base_dir).unwrap_or(path).to_string_lossy();
      writeln!(
         err_stream,
         "↳ {} @ line {}, column {} [{}]",
         description,
         line + 1,
         col + 1,
         path_str,
      )
      .unwrap();
   } else {
      writeln!(err_stream, "↳ {} @ line {}, column {}", description, line + 1, col + 1).unwrap();
   }
}
