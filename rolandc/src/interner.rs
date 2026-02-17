use std::mem;
use std::num::NonZeroUsize;

use hashbrown::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct StrId(NonZeroUsize);

// TODO: remove this, we only use it for a dumb reason
pub const DUMMY_STR_TOKEN: StrId = StrId(NonZeroUsize::new(1).unwrap());

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
      let len = self.map.len();
      match self.map.raw_entry_mut().from_key(name) {
         hashbrown::hash_map::RawEntryMut::Occupied(o) => StrId(*o.get()),
         hashbrown::hash_map::RawEntryMut::Vacant(v) => {
            let name = unsafe { alloc(&mut self.buf, &mut self.full, name) };
            // Obviously safe, due to the +1
            let id = unsafe { NonZeroUsize::new_unchecked(len.checked_add(1).unwrap()) };
            v.insert(name, id);
            self.vec.push(name);

            debug_assert!(self.lookup(StrId(id)) == name);
            debug_assert!(self.intern(name) == StrId(id));

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

unsafe fn alloc(buf: &mut String, full: &mut Vec<String>, name: &str) -> &'static str {
   let cap = buf.capacity();
   if cap < buf.len() + name.len() {
      let new_cap = (cap.max(name.len()) + 1).next_power_of_two();
      let new_buf = String::with_capacity(new_cap);
      let old_buf = mem::replace(buf, new_buf);
      full.push(old_buf);
   }

   let interned = {
      let start = buf.len();
      buf.push_str(name);
      &buf[start..]
   };

   unsafe { &*std::ptr::from_ref(interned) }
}
