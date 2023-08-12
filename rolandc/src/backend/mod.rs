use crate::interner::Interner;
use crate::{CompilationConfig, Program};

pub mod linearize;
mod liveness;
mod regalloc;
mod wasm;

pub fn emit_wasm(program: &mut Program, interner: &mut Interner, config: &CompilationConfig) -> Vec<u8> {
   program.cfg = linearize::linearize(program, interner, config.dump_debugging_info);

   wasm::emit_wasm(program, interner, config)
}
