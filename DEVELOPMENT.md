This guide aims to document basic workflows for developing the Roland compiler.

# Prerequisites

In order to build the compiler, you will need the standard [rust toolchain](https://rustup.rs/). In order to run tests and run other scripts associated with this project, you will need [just](https://github.com/casey/just?tab=readme-ov-file#installation).¹

For the native backend to work, you will need `qbe` installed. For running tests using the WASM backend, you will need `wasmtime` installed.

All commands that follow in this document are intended to be run in the root directory of this project. That is, the same directory containing this file.

¹*It is possible to get away without having `just` installed - look in the `justfile` to see what commands `just` would be running, and run them yourself.*

## Obtaining QBE

`qbe` may be available form your distro's package manager. Failing that, check out the [qbe site](https://c9x.me/compile/releases.html).

## Obtaining wasmtime

`wasmtime` may be available from your distro's package manager. Failing that, check out [the wasmtime documentation](https://docs.wasmtime.dev/cli-install.html).

# Running Tests
`just test_amd64`

This command will automatically build the compiler if necessary, and run all tests using the QBE linux-amd64 backend.

Test artifacts will be cleaned up automatically for passing tests. Artifacts for faiiling tests (such as .s and .ssa files) will stick around for inspection.

## Comparing generated code before/after
`just baseline`  
...(change rolandc, qbe, etc.)...  
`just test-all-preserve-artifacts`  

The first command runs all tests, saving artifacts into the folder `tests_baseline`. The second runs all tests again, saving artifacts into the normal `tests` folder.

Then, use your favorite folder diff tool to see what changed in the generated code.

## Overriding QBE
By default, the roland compiler will look for QBE on the system `PATH`. If you are working on QBE and want to test your changes without overriding the system installation of QBE, you can place your binary in `target/release/` and the roland compiler should automatically pick it up and use it instead.
