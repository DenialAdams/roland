if [ $OSTYPE == "cygwin" ];
then
   cargo build --release && ./target/release/roland_test_runner.exe tests/ `cygpath -d --absolute ./target/release/rolandc_cli.exe`
else
   cargo build --release && ./target/release/roland_test_runner tests/ `readlink --canonicalize ./target/release/rolandc_cli`
fi
