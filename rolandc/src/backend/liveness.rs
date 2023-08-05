use indexmap::IndexMap;

use super::linearize::{BasicBlock, Cfg};
use crate::parse::VariableId;
use crate::semantic_analysis::GlobalInfo;

pub struct LivenessResult {}

#[must_use]
pub fn liveness(cfg: &Cfg, globals: &IndexMap<VariableId, GlobalInfo>) -> LivenessResult {
   LivenessResult {}
}
