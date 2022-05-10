cargo build --release --bin rolandc_cli &> /dev/null


compiled_ok=1

target/release/rolandc_cli --wasm4 w4-games/spunky/cart.rol
if [ "$?" -ne 0 ]; then
  compiled_ok=0
fi
target/release/rolandc_cli --wasm4 w4-games/endless-runner/cart.rol
if [ "$?" -ne 0 ]; then
  compiled_ok=0
fi
test "$compiled_ok" -ne 0
