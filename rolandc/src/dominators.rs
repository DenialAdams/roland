use std::collections::{HashMap, HashSet};

use crate::backend::linearize::{post_order, Cfg};

#[derive(Debug)]
pub struct DominatorTree {
    pub children: HashMap<usize, HashSet<usize>>,
}

pub fn compute_dominators(cfg: &Cfg) -> DominatorTree {
    let rpo: Vec<usize> = post_order(cfg).into_iter().rev().collect();
    let cfg_index_to_rpo_index: HashMap<usize, usize> = rpo.iter().enumerate().map(|(i, x)| (*x, i)).collect();
    let mut dominators = vec![None; rpo.len()];
    debug_assert!(cfg_index_to_rpo_index[&cfg.start] == 0);
    dominators[0] = Some(0);
    let mut changed = true;
    while changed {
        changed = false;
        for b in 1..rpo.len() {
            let mut preds: Vec<usize> = cfg.bbs[rpo[b]].predecessors.iter().copied().filter_map(|x| cfg_index_to_rpo_index.get(&x)).copied().collect();
            preds.sort_unstable();
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
    for elem in dominators.iter() {
        dt.children.entry(dominators[elem.unwrap()].unwrap()).or_default().insert(elem.unwrap());
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