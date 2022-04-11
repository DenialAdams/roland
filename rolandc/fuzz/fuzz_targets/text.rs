#![no_main]
use std::io::Write;

use libfuzzer_sys::fuzz_target;

struct NulWriter;

impl Write for NulWriter {
   fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
      Ok(buf.len())
   }

   fn flush(&mut self) -> std::io::Result<()> {
      Ok(())
   }
}

fuzz_target!(|data: &[u8]| {
   if let Ok(s) = std::str::from_utf8(data) {
      // By using the wasm4 target, we compile the emitted WAT to bytes
      // (although this fuzzer doesn't produce programs that make it that far)
      let mut ctx = rolandc::CompilationContext::new();
      let _ = rolandc::compile::<NulWriter>(&mut ctx, rolandc::CompilationEntryPoint::Buffer(s), &mut NulWriter {}, rolandc::Target::Wasm4);
   }
});
