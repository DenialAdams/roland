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
   let _ = rolandc::compile_for_fuzzer::<NulWriter, NulWriter>(data, &mut NulWriter {}, None, true, rolandc::Target::Wasm4);
});
