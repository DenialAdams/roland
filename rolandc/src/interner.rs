use std::{mem::ManuallyDrop, num::NonZeroUsize};

use bumpalo::Bump;
use hashbrown::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct StrId(NonZeroUsize);

// TODO: remove this, we only use it for a dumb reason
pub const DUMMY_STR_TOKEN: StrId = StrId(NonZeroUsize::new(1).unwrap());

struct Alloc {
   bump: bumpalo::Bump,
}

unsafe impl Sync for Alloc {}
unsafe impl Send for Alloc {}

pub struct Interner {
   map: HashMap<&'static str, NonZeroUsize>,
   vec: Vec<&'static str>,
   alloc: Alloc,
}

impl Interner {
   #[must_use]
   pub fn new() -> Interner {
      Interner {
         map: HashMap::default(),
         vec: vec![""],
         alloc: Alloc { bump: Bump::new() },
      }
   }

   pub fn intern(&mut self, name: &str) -> StrId {
      let len = self.map.len();
      match self.map.raw_entry_mut().from_key(name) {
         hashbrown::hash_map::RawEntryMut::Occupied(o) => StrId(*o.get()),
         hashbrown::hash_map:: RawEntryMut::Vacant(v) => {
            let alloc = ManuallyDrop::new(bumpalo::collections::String::from_str_in(name, &self.alloc.bump));
            let name: &'static str = unsafe { &*std::ptr::from_ref(alloc.as_str()) };
            // Obviously safe, due to the +1
            let id = unsafe { NonZeroUsize::new_unchecked(len.checked_add(1).unwrap()) };
            v.insert(name, id);
            self.vec.push(name);

            debug_assert_eq!(self.lookup(StrId(id)), name);
            debug_assert_eq!(self.intern(name), StrId(id));

            StrId(id)
         }
      }
   }

   #[must_use]
   pub fn lookup(&self, id: StrId) -> &str {
      self.vec[id.0.get()]
   }

   #[must_use]
   pub fn reverse_lookup(&self, name: &str) -> Option<StrId> {
      self.map.get(name).map(|x| StrId(*x))
   }
}
