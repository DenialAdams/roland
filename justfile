release_flag := if env_var_or_default("DEBUG", "false") == "true" { "" } else { "--release" }

test path="tests/":
   cargo run {{release_flag}} --bin roland_test_runner -- {{path}}
test-overwrite:
   cargo run {{release_flag}} --bin roland_test_runner -- tests/ --overwrite-error-files
samples:
   cargo run {{release_flag}} --bin rolandc_cli -- --wasm4 samples/wasm4/spunky/cart.rol
   cargo run {{release_flag}} --bin rolandc_cli -- --wasm4 samples/wasm4/endless-runner/cart.rol
   cargo run {{release_flag}} --bin rolandc_cli -- --microw8 samples/microw8/tunnel/tunnel.rol
   @echo "Samples OK!"
update-deps:
   cargo update
   cd roland-vscode && npm update
scratch:
   cargo run {{release_flag}} --bin rolandc_cli -- scratch.rol
   wasmtime scratch.wat
coverage:
   mv tests/ roland_test_runner/tests/
   cargo tarpaulin --skip-clean --implicit-test-threads --command build --bin roland_test_runner -o html -- tests/
   mv roland_test_runner/tests/ tests/
   {{env_var_or_default("BROWSER", "firefox")}} "file://`readlink -f tarpaulin-report.html`#rolandc/src"
