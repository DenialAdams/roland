OVERWRITE_PARAMS=""
if [[ $TEST_RUNNER_DO_OVERWRITE_ERR == "true" ]];
then
   read -p "DESTRUCTIVELY OVERWRITING OUTPUT. Press any key to continue" -n 1 -r
   OVERWRITE_PARAMS="--overwrite-error-files"
fi

if [[ $DEBUG == "true" ]];
then
   if [ $OSTYPE == "cygwin" ];
   then
      cargo build && ./target/debug/roland_test_runner.exe tests/ `cygpath -d --absolute ./target/debug/rolandc_cli.exe` $OVERWRITE_PARAMS
   else
      cargo build && ./target/debug/roland_test_runner tests/ `readlink --canonicalize ./target/debug/rolandc_cli` $OVERWRITE_PARAMS
   fi
else
   if [ $OSTYPE == "cygwin" ];
   then
      cargo build --release && ./target/release/roland_test_runner.exe tests/ `cygpath -d --absolute ./target/release/rolandc_cli.exe` $OVERWRITE_PARAMS
   else
      cargo build --release && ./target/release/roland_test_runner tests/ `readlink --canonicalize ./target/release/rolandc_cli` $OVERWRITE_PARAMS
   fi
fi
