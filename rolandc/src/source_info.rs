#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourcePosition {
   pub line: usize,
   pub col: usize,
}

impl SourcePosition {
   #[must_use]
   pub fn next_col(&self) -> SourcePosition {
      self.col_plus(1)
   }

   #[must_use]
   pub fn col_plus(&self, n: usize) -> SourcePosition {
      SourcePosition {
         line: self.line,
         col: self.col + n,
      }
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
         begin: SourcePosition { line: 0, col: 0 },
         end: SourcePosition { line: 0, col: 0 },
         file: SourcePath(usize::MAX),
      }
   }
}

// TODO: killing this enum
// Instead sourcepath is an index into an IndexMap<(PathBuf, bool), String> map
// bool is for std.
// benefits: SourcePath will be smaller AND we can get the PathBuf exactly back instead of having to go through StrId which is lossy
// AND AND we have a clear place to stick the damn file contents so we can get them back for error reporting. ka-boom.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SourcePath(pub usize);
