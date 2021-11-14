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
      let _ = rolandc::compile::<NulWriter, NulWriter>(s, &mut NulWriter {}, None, true, rolandc::Target::Wasm4);
   }
});
