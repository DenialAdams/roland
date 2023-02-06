use std::cell::Cell;

#[derive(Clone, Debug)]
pub struct DisjointSet {
   tree: Vec<Cell<Node>>,
}

#[derive(Clone, Copy, Debug)]
struct Node {
   parent: usize,
   rank: usize,
}

impl DisjointSet {
   pub fn new() -> DisjointSet {
      DisjointSet { tree: Vec::new() }
   }

   pub fn add_new_set(&mut self) -> usize {
      let old_len = self.tree.len();
      self.tree.push(Cell::new(Node {
         parent: old_len,
         rank: 0,
      }));
      old_len
   }

   // find with path compression
   pub fn find(&self, x: usize) -> usize {
      let mut at_x = self.tree[x].get();
   
      let current_parent = at_x.parent;
      if current_parent != x {
         at_x.parent = self.find(current_parent);
      }

      self.tree[x].set(at_x);

      at_x.parent
   }

   // union by rank
   pub fn union(&self, x: usize, y: usize) {
      let x_root = self.find(x);
      let y_root = self.find(y);

      if x_root == y_root {
         return;
      }

      let mut at_x = self.tree[x_root].get();
      let mut at_y = self.tree[y_root].get();

      let (x_root, y_root) = if at_x.rank < at_y.rank {
         (y_root, x_root)
      } else {
         (x_root, y_root)
      };

      at_x = self.tree[x_root].get();
      at_y = self.tree[y_root].get();

      at_y.parent = x_root;
      if at_x.rank == at_y.rank {
         at_x.rank += 1;
      }

      self.tree[x_root].set(at_x);
      self.tree[y_root].set(at_y);
   }
}
