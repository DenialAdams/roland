#[derive(Clone, Debug)]
pub struct DisjointSet {
   tree: Vec<Node>,
}

#[derive(Clone, Debug)]
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
      self.tree.push(Node {
         parent: old_len,
         rank: 0,
      });
      old_len
   }

   // find with path compression
   pub fn find(&mut self, x: usize) -> usize {
      let current_parent = self.tree[x].parent;
      if current_parent != x {
         self.tree[x].parent = self.find(current_parent);
      }
      self.tree[x].parent
   }

   // union by rank
   pub fn union(&mut self, x: usize, y: usize) {
      let x_root = self.find(x);
      let y_root = self.find(y);

      if x_root == y_root {
         return;
      }

      let (x_root, y_root) = if self.tree[x_root].rank < self.tree[y_root].rank {
         (y_root, x_root)
      } else {
         (x_root, y_root)
      };

      self.tree[y_root].parent = x_root;
      if self.tree[x_root].rank == self.tree[y_root].rank {
         self.tree[x_root].rank += 1;
      }
   }
}
