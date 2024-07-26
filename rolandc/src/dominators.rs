use std::collections::HashMap;

use indexmap::IndexSet;

use crate::backend::linearize::Cfg;

#[derive(Debug)]
pub struct DominatorTree {
   pub children: HashMap<usize, IndexSet<usize>>,
}

pub fn compute_dominators(cfg: &Cfg, rpo: &[usize]) -> DominatorTree {
   let cfg_index_to_rpo_index: HashMap<usize, usize> = rpo.iter().enumerate().map(|(i, x)| (*x, i)).collect();
   let mut dominators = vec![None; rpo.len()];
   debug_assert!(cfg_index_to_rpo_index[&cfg.start] == 0);
   dominators[0] = Some(0);
   let mut changed = true;
   while changed {
      changed = false;
      for b in 1..rpo.len() {
         let mut preds: Vec<usize> = cfg.bbs[rpo[b]]
            .predecessors
            .iter()
            .copied()
            .filter_map(|x| cfg_index_to_rpo_index.get(&x))
            .copied()
            .collect();
         preds.sort_unstable();
         let new_idom = preds.iter().copied().fold(preds.first().copied().unwrap(), |acc, p| {
            intersect(acc, p, &dominators)
         });
         if dominators[b] != Some(new_idom) {
            dominators[b] = Some(new_idom);
            changed = true;
         }
      }
   }
   let mut dt = DominatorTree {
      children: HashMap::with_capacity(dominators.len()),
   };
   dbg!(&dominators);
   for elem in dominators.iter().map(|x| x.unwrap()) {
      if elem == 0 {
         // The start node must be dominated by itself only
         continue;
      }
      dt.children.entry(dominators[elem].unwrap()).or_default().insert(elem);
   }
   for children_list in dt.children.values_mut() {
      children_list.sort_unstable();
   }
   dt
}

fn intersect(a: usize, b: usize, doms: &[Option<usize>]) -> usize {
   let mut finger1 = a;
   let mut finger2 = b;
   while finger1 != finger2 {
      while finger1 > finger2 {
         finger1 = doms[finger1].unwrap();
      }
      while finger2 > finger1 {
         finger2 = doms[finger2].unwrap();
      }
   }
   finger1
}
