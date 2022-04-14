#![no_main]
use std::io::Write;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
   if let Ok(s) = std::str::from_utf8(data) {
      // By using the wasm4 target, we compile the emitted WAT to bytes
      // (although this fuzzer doesn't produce programs that make it that far)
      let mut ctx = rolandc::CompilationContext::new();
      let _ = rolandc::compile(&mut ctx, rolandc::CompilationEntryPoint::Buffer(s), rolandc::Target::Wasm4);
   }
});
