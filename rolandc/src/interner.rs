use std::collections::HashMap;
use std::mem;
use std::num::NonZeroUsize;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct StrId(NonZeroUsize);

// TODO: remove this, we only use it for a dumb reason
// Obviously safe, but we can't use the safe constructor until const unwrap
pub const DUMMY_STR_TOKEN: StrId = StrId(unsafe { NonZeroUsize::new_unchecked(1) });

pub struct Interner {
   map: HashMap<&'static str, NonZeroUsize>,
   vec: Vec<&'static str>,
   buf: String,
   full: Vec<String>,
}

impl Interner {
   #[must_use]
   pub fn with_capacity(cap: usize) -> Interner {
      let cap = cap.next_power_of_two();
      Interner {
         map: HashMap::default(),
         vec: vec![""],
         buf: String::with_capacity(cap),
         full: Vec::new(),
      }
   }

   pub fn intern(&mut self, name: &str) -> StrId {
      if let Some(&id) = self.map.get(name) {
         return StrId(id);
      }
      let name = unsafe { self.alloc(name) };
      // Obviously safe, due to the +1
      let id = unsafe { NonZeroUsize::new_unchecked(self.map.len() + 1) };
      self.map.insert(name, id);
      self.vec.push(name);

      debug_assert!(self.lookup(StrId(id)) == name);
      debug_assert!(self.intern(name) == StrId(id));

      StrId(id)
   }

   #[must_use]
   pub fn lookup(&self, id: StrId) -> &str {
      self.vec[id.0.get()]
   }

   #[must_use]
   pub fn reverse_lookup(&self, name: &str) -> Option<StrId> {
      self.map.get(name).map(|x| StrId(*x))
   }

   unsafe fn alloc(&mut self, name: &str) -> &'static str {
      let cap = self.buf.capacity();
      if cap < self.buf.len() + name.len() {
         let new_cap = (cap.max(name.len()) + 1).next_power_of_two();
         let new_buf = String::with_capacity(new_cap);
         let old_buf = mem::replace(&mut self.buf, new_buf);
         self.full.push(old_buf);
      }

      let interned = {
         let start = self.buf.len();
         self.buf.push_str(name);
         &self.buf[start..]
      };

      &*std::ptr::from_ref(interned)
   }
}
