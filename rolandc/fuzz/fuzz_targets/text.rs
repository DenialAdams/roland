#![no_main]
use libfuzzer_sys::fuzz_target;

use std::borrow::Cow;
use std::path::{Path, PathBuf};

struct FuzzFileResolver<'a> {
   source: &'a str,
}

const FUZZ_PATH: &str = "fuzz";

use rolandc::FileResolver;

impl FileResolver for FuzzFileResolver<'_> {
   const REQUIRES_CANONIZATION: bool = false;
   fn resolve_path<'a>(&'a mut self, path: &std::path::Path) -> std::io::Result<Cow<'a, str>> {
      if path == Path::new(FUZZ_PATH) {
         return Ok(Cow::Borrowed(self.source));
      }
      Err(std::io::Error::new(std::io::ErrorKind::Unsupported, "Files can't be imported with the fuzzer"))
   }
}

fuzz_target!(|data: &[u8]| {
   if let Ok(s) = std::str::from_utf8(data) {
      let mut ctx = rolandc::CompilationContext::new();
      let _ = rolandc::compile::<FuzzFileResolver>(&mut ctx, rolandc::CompilationEntryPoint {
         ep_path: PathBuf::from(FUZZ_PATH),
         resolver: FuzzFileResolver { source: s },
      }, &rolandc::CompilationConfig {
         target: rolandc::Target::QbeFreestanding,
         include_std: true,
         i_am_std: false,
         dump_debugging_info: false,
      });
   }
});
