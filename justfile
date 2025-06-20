release_flag := if env_var_or_default("DEBUG", "0") == "1" { "" } else { "--release" }
release_text := if env_var_or_default("DEBUG", "0") == "1" { "debug" } else { "release" }

test path="tests/":
   cargo build {{release_flag}} --bin rolandc_cli
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli {{path}}
test_amd64 path="tests/":
   cargo build {{release_flag}} --bin rolandc_cli
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli {{path}} --amd64
test-overwrite:
   cargo build {{release_flag}} --bin rolandc_cli
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli tests/ --overwrite-error-files
samples:
   cargo run {{release_flag}} --bin rolandc_cli -- --wasm4 samples/wasm4/spunky/cart.rol
   cargo run {{release_flag}} --bin rolandc_cli -- --wasm4 samples/wasm4/endless-runner/cart.rol
   cargo run {{release_flag}} --bin rolandc_cli -- --microw8 samples/microw8/tunnel/tunnel.rol
   @echo "Samples OK!"
bump-deps:
   cargo update
   cd roland-vscode && npm update
   cd roland_site && npm update
scratch *args:
   cargo run {{release_flag}} --bin rolandc_cli -- scratch.rol {{args}}
   wasm2wat --no-check scratch.wasm > scratch.wat
   wasmtime scratch.wasm
scratch_amd64 *args:
   cargo run {{release_flag}} --bin rolandc_cli -- scratch.rol {{args}} --target amd64 && ./scratch
coverage:
   cargo clean
   RUSTFLAGS="-Cinstrument-coverage -Cstrip=none -Clink-dead-code -Cdebuginfo=2" cargo build --bin rolandc_cli
   cargo tarpaulin --skip-clean --implicit-test-threads --follow-exec --engine llvm --command build --bin roland_test_runner -o html -- {{justfile_directory()}}/tests/ --cli {{justfile_directory()}}/target/debug/rolandc_cli
   {{env_var_or_default("BROWSER", "firefox")}} "{{justfile_directory()}}/tarpaulin-report.html#rolandc/src"
[no-cd]
rolandc *args:
   cargo run {{release_flag}} --bin rolandc_cli -- {{args}}
[no-cd]
rolandc_dhat *args:
   cargo run --profile dhat --bin rolandc_cli --features dhat-heap -- {{args}}
[no-cd]
rolandc_flame *args:
   cargo flamegraph --profile dhat --freq 100000 --bin rolandc_cli -- {{args}}
[no-cd]
rolandc_samply *args:
   cargo build --profile dhat
   samply record -r 10000 {{justfile_directory()}}/target/dhat/rolandc_cli {{args}}
prepare-release kind="patch":
   cd roland-vscode && npm version {{kind}}
   cd roland_site && npm version {{kind}}
   cd rolandc_web/pkg && npm version {{kind}}
test-all:
   cargo build {{release_flag}} --bin rolandc_cli
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli tests/ --amd64
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli tests/
test-all-preserve-artifacts:
   cargo build {{release_flag}} --bin rolandc_cli
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli tests/ --amd64 --preserve-artifacts
   cargo run --release --bin roland_test_runner -- --cli {{justfile_directory()}}/target/{{release_text}}/rolandc_cli tests/ --preserve-artifacts
baseline: test-all-preserve-artifacts
   rm -rf tests_baseline/
   cp -r tests/ tests_baseline/
