#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SourcePath(pub usize);
