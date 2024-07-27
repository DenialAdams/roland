#![no_main]
use libfuzzer_sys::fuzz_target;

struct PlaygroundFileResolver;

use rolandc::FileResolver;

impl<'a> FileResolver<'a> for PlaygroundFileResolver {
   fn resolve_path(&mut self, _path: &std::path::Path) -> std::io::Result<std::borrow::Cow<'a, str>> {
      unreachable!()
   }
}

fuzz_target!(|data: &[u8]| {
   if let Ok(s) = std::str::from_utf8(data) {
      let mut ctx = rolandc::CompilationContext::new();
      let _ = rolandc::compile::<PlaygroundFileResolver>(&mut ctx, rolandc::CompilationEntryPoint::Playground(s), &rolandc::CompilationConfig {
         target: rolandc::Target::Qbe,
         include_std: true,
         i_am_std: false,
         dump_debugging_info: false,
      });
   }
});
