use crate::interner::StrId;

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourcePath {
   Sandbox,
   Std(StrId),
   File(StrId),
}
