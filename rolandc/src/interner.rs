use std::{alloc::Layout, hash::BuildHasher};
use std::num::NonZeroUsize;

use bumpalo::Bump;
use hashbrown::{DefaultHashBuilder, HashMap};
use parking_lot::Mutex;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct StrId(NonZeroUsize);

// TODO: remove this, we only use it for a dumb reason
pub const DUMMY_STR_TOKEN: StrId = StrId(NonZeroUsize::new(1).unwrap());

struct Shard {
   bump: bumpalo::Bump,
   map: Mutex<HashMap<&'static str, NonZeroUsize>>,
}

// Safety: bump is only accessed while we are holding the map lock.
unsafe impl Sync for Shard {}

pub struct Interner {
   shards: Vec<Shard>,
   hasher: DefaultHashBuilder,
}

impl Interner {
   #[must_use]
   pub fn new() -> Interner {
      let num_threads = rayon::current_num_threads();
      let num_shards = if num_threads == 1 {
         1
      } else {
         (num_threads * 2).next_power_of_two().clamp(4, 64)
      };
      let hasher = hashbrown::DefaultHashBuilder::default();
      let shards = (0..num_shards).map(|_| Shard { bump: Bump::new(), map: Mutex::new(HashMap::with_hasher(hasher.clone())) }).collect();
      Interner {
         shards,
         hasher,
      }
   }

   #[must_use]
   pub fn intern(&self, name: &str) -> StrId {
      let hash = self.hasher.hash_one(name);
      let shard_idx = hash & (self.shards.len() as u64 - 1);
      let shard = &self.shards[shard_idx as usize];
      let mut map = shard.map.lock();
      match map.raw_entry_mut().from_hash(hash, |k| *k == name) {
         hashbrown::hash_map::RawEntryMut::Occupied(o) => StrId(*o.get()),
         hashbrown::hash_map::RawEntryMut::Vacant(v) => {
            let alloc = shard.bump.alloc_layout(
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
            //let name: &'static str = unsafe { std::str::from_raw_parts(alloc.as_ptr().add(std::mem::size_of::<usize>()), name.len()) };
            v.insert_hashed_nocheck(hash, name, alloc.addr());

            StrId(alloc.addr())
         }
      }
   }

   #[must_use]
   pub fn lookup(&self, id: StrId) -> &str {
      // This function is definitely not safe if the StrId came from another interner. But it's ok.

      let ptr = id.0.get() as *const usize;
      let len = unsafe { ptr.read() };

      unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr.add(1).cast(), len)) }
   }

   #[must_use]
   pub fn reverse_lookup(&self, name: &str) -> Option<StrId> {
      let hash = self.hasher.hash_one(name);
      let shard_idx = hash & (self.shards.len() as u64 - 1);
      let shard = &self.shards[shard_idx as usize];
      let map = shard.map.lock();
      map.get(name).map(|x| StrId(*x))
   }
}
