#![no_main]
use libfuzzer_sys::fuzz_target;

use std::borrow::Cow;
use std::path::{Path, PathBuf};

use rolandc::FileResolver;

struct FuzzFileResolver<'a> {
   source: &'a str,
}

const FUZZ_PATH: &str = "fuzz";

impl FileResolver for FuzzFileResolver<'_> {
   fn resolve_path(&mut self, path: &Path) -> std::io::Result<Cow<'static, str>> {
      if path == Path::new(FUZZ_PATH) {
         return Ok(Cow::Owned(self.source.to_owned()));
      }
      Err(std::io::Error::new(
         std::io::ErrorKind::Unsupported,
         "Files can't be imported with the fuzzer",
      ))
   }

   fn canonicalize_path<'a>(&'a self, path: &'a Path) -> std::io::Result<Cow<'a, Path>> {
      Ok(Cow::Borrowed(path))
   }
}

fuzz_target!(|data: &[u8]| {
   if let Ok(s) = std::str::from_utf8(data) {
      let mut ctx = rolandc::CompilationContext::new();
      let mut resolver = FuzzFileResolver { source: s };
      let _ = rolandc::compile(
         &mut ctx,
         rolandc::CompilationEntryPoint {
            ep_path: PathBuf::from(FUZZ_PATH),
            resolver: &mut resolver,
         },
         &rolandc::CompilationConfig {
            target: rolandc::Target::QbeFreestanding,
            include_std: true,
            i_am_std: false,
            dump_debugging_info: false,
         },
      );
   }
});
