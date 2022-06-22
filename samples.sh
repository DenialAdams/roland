cargo build --release --bin rolandc_cli &> /dev/null

compiled_ok=1

target/release/rolandc_cli --wasm4 samples/wasm4/spunky/cart.rol
if [ "$?" -ne 0 ]; then
  compiled_ok=0
fi
target/release/rolandc_cli --wasm4 samples/wasm4/endless-runner/cart.rol
if [ "$?" -ne 0 ]; then
  compiled_ok=0
fi
target/release/rolandc_cli --microw8 samples/microw8/tunnel/tunnel.rol
if [ "$?" -ne 0 ]; then
  compiled_ok=0
fi

test "$compiled_ok" -ne 0
