use crate::interner::Interner;
use crate::{Program, Target};

mod linearize;
mod liveness;
mod regalloc;
mod wasm;

pub fn emit_wasm(program: &mut Program, interner: &mut Interner, target: Target) -> Vec<u8> {
   wasm::emit_wasm(program, interner, target)
}
