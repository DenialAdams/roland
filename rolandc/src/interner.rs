use std::alloc::Layout;
use std::num::NonZeroUsize;

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
   alloc: Alloc,
}

impl Interner {
   #[must_use]
   pub fn new() -> Interner {
      Interner {
         map: HashMap::default(),
         alloc: Alloc { bump: Bump::new() },
      }
   }

   pub fn intern(&mut self, name: &str) -> StrId {
      match self.map.raw_entry_mut().from_key(name) {
         hashbrown::hash_map::RawEntryMut::Occupied(o) => StrId(*o.get()),
         hashbrown::hash_map::RawEntryMut::Vacant(v) => {
            let alloc = self.alloc.bump.alloc_layout(
               Layout::from_size_align(name.len() + std::mem::size_of::<usize>(), std::mem::align_of::<usize>())
                  .unwrap(),
            );
            unsafe {
               alloc.cast::<usize>().write(name.len());
               std::ptr::copy_nonoverlapping(
                  name.as_ptr(),
                  alloc.as_ptr().add(std::mem::size_of::<usize>()),
                  name.len(),
               );
            }

            let name = unsafe {
               std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                  alloc.as_ptr().add(std::mem::size_of::<usize>()),
                  name.len(),
               ))
            };
            // TODO: when str::from_raw_parts is stabilized
            //let name: &'static str = unsafe { std::str::from_raw_parts(alloc.as_ptr(), name.len()) };
            v.insert(name, alloc.addr());

            StrId(alloc.addr())
         }
      }
   }

   #[must_use]
   pub fn lookup(&self, id: StrId) -> &str {
      // This function is definitely not safe if the StrId came from another interner. But it's ok.

      let ptr = id.0.get() as *const u8;
      #[allow(clippy::cast_ptr_alignment)]
      let len = unsafe { ptr.cast::<usize>().read() };
      // TODO: when try_cast_aligned is stabilized to get rid of the clippy warning?
      //let len = unsafe { ptr.try_cast_aligned::<usize>().unwrap_unchecked().read() };

      unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr.add(std::mem::size_of::<usize>()), len)) }
   }

   #[must_use]
   pub fn reverse_lookup(&self, name: &str) -> Option<StrId> {
      self.map.get(name).map(|x| StrId(*x))
   }
}
