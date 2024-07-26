use std::collections::HashMap;

use indexmap::IndexSet;

use crate::backend::linearize::Cfg;

#[derive(Debug)]
pub struct DominatorTree {
   pub children: HashMap<usize, IndexSet<usize>>,
}

pub fn compute_dominators(cfg: &Cfg, rpo: &[usize], cfg_index_to_rpo_index: &HashMap<usize, usize>) -> DominatorTree {
   let mut dominators = vec![None; rpo.len()];
   debug_assert!(cfg_index_to_rpo_index[&cfg.start] == 0);
   dominators[0] = Some(0);
   let mut changed = true;
   while changed {
      changed = false;
      for b in 1..rpo.len() {
         let preds: Vec<usize> = cfg.bbs[rpo[b]]
            .predecessors
            .iter()
            .copied()
            .filter_map(|x| cfg_index_to_rpo_index.get(&x))
            .copied()
            .collect();
         let mut new_idom = preds.iter().copied().find(|x| dominators[*x].is_some()).unwrap();
         let first_p = new_idom;
         for p in preds.iter().copied().filter(|x| *x != first_p) {
            if dominators[p].is_some() {
               new_idom = intersect(p, new_idom, &dominators);
            }
         }
         if dominators[b] != Some(new_idom) {
            dominators[b] = Some(new_idom);
            changed = true;
         }
      }
   }
   let mut dt = DominatorTree {
      children: HashMap::with_capacity(dominators.len()),
   };
   for (i, elem) in dominators.into_iter().map(|x| x.unwrap()).enumerate().skip(1) {
      dt.children.entry(elem).or_default().insert(i);
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
