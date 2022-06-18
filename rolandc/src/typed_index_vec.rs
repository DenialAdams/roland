// This code from @rpjohnst is used and modified under the MIT license:
/*
Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
*/

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// A Handle is a typed index into a table of some sort of data
pub trait Handle: Copy + Eq {
   fn new(_: usize) -> Self;
   fn index(self) -> usize;
}

#[derive(Clone)]
pub struct HandleMap<K, V>
where
   K: Handle,
{
   keys: PhantomData<K>,
   pub values: Vec<V>,
}

impl<K, V> Default for HandleMap<K, V>
where
   K: Handle,
{
   fn default() -> Self {
      HandleMap {
         keys: PhantomData,
         values: Vec::default(),
      }
   }
}

impl<K, V> HandleMap<K, V>
where
   K: Handle,
{
   pub fn new() -> Self {
      Self::default()
   }

   pub fn clear(&mut self) {
      self.values.clear();
   }

   pub fn len(&self) -> usize {
      self.values.len()
   }

   pub fn get(&self, k: K) -> Option<&V> {
      self.values.get(k.index())
   }

   pub fn push(&mut self, v: V) -> K {
      let k = self.next_key();
      self.values.push(v);
      k
   }

   fn next_key(&self) -> K {
      K::new(self.values.len())
   }
}

impl<K, V> Index<K> for HandleMap<K, V>
where
   K: Handle,
{
   type Output = V;

   fn index(&self, k: K) -> &V {
      &self.values[k.index()]
   }
}

impl<K, V> IndexMut<K> for HandleMap<K, V>
where
   K: Handle,
{
   fn index_mut(&mut self, k: K) -> &mut V {
      &mut self.values[k.index()]
   }
}

pub struct Keys<K> {
   pos: usize,
   len: usize,
   key: PhantomData<K>,
}

impl<K> Iterator for Keys<K>
where
   K: Handle,
{
   type Item = K;

   fn next(&mut self) -> Option<Self::Item> {
      if self.pos < self.len {
         let key = K::new(self.pos);
         self.pos += 1;
         Some(key)
      } else {
         None
      }
   }

   fn size_hint(&self) -> (usize, Option<usize>) {
      let len = self.len - self.pos;
      (len, Some(len))
   }
}

impl<K> DoubleEndedIterator for Keys<K>
where
   K: Handle,
{
   fn next_back(&mut self) -> Option<Self::Item> {
      if self.pos < self.len {
         self.len -= 1;
         let key = K::new(self.len);
         Some(key)
      } else {
         None
      }
   }
}

impl<K> ExactSizeIterator for Keys<K> where K: Handle {}
