use crate::FileMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct SourcePosition(pub usize);

impl SourcePosition {
   #[must_use]
   pub fn next_index(&self) -> SourcePosition {
      self.index_plus(1)
   }

   #[must_use]
   pub fn index_plus(&self, n: usize) -> SourcePosition {
      SourcePosition(self.0 + n)
   }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceInfo {
   pub begin: SourcePosition,
   pub end: SourcePosition,
   pub file: SourcePath,
}

impl SourceInfo {
   #[must_use]
   pub fn dummy() -> SourceInfo {
      SourceInfo {
         begin: SourcePosition(0),
         end: SourcePosition(0),
         file: SourcePath(usize::MAX),
      }
   }
}

impl SourceInfo {
   #[must_use]
   pub fn cmp_with_filemap(&self, other: &Self, files: &FileMap) -> std::cmp::Ordering {
      let ((this_path, this_is_std), _) = files.get_index(self.file.0).unwrap();
      let ((other_path, other_is_std), _) = files.get_index(other.file.0).unwrap();
      let std_cmp = this_is_std.cmp(other_is_std);
      if std_cmp != std::cmp::Ordering::Equal {
         return std_cmp.reverse();
      }
      this_path
         .cmp(other_path)
         .then_with(|| self.begin.cmp(&other.begin))
         .then_with(|| self.end.cmp(&other.end))
   }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SourcePath(pub usize);
