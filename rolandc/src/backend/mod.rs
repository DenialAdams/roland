use crate::interner::Interner;
use crate::{Program, CompilationConfig};

mod linearize;
mod liveness;
mod regalloc;
mod wasm;

pub fn emit_wasm(program: &mut Program, interner: &mut Interner, config: &CompilationConfig) -> Vec<u8> {
   wasm::emit_wasm(program, interner, config)
}
