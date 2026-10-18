#![allow(clippy::result_unit_err)] // We report the error before rutrning

#[cfg(target_os = "linux")]
pub fn link(linker_args: &[std::ffi::OsString]) -> Result<(), ()> {
   let args = {
      let arg_fn = || linker_args.iter().map(|s| s.to_str().unwrap());

      let mut args = libwild::Args::new(arg_fn).unwrap();
      args.parse(arg_fn).unwrap();
      args
   };

   let linker = libwild::Linker::new();
   linker.run(&args).map(|_| ()).map_err(|e| {
      libwild::error::report_error(&e);
   })
}
