OVERWRITE_PARAMS=""
RELEASE="--release"
if [[ $TEST_RUNNER_DO_OVERWRITE_ERR == "true" ]];
then
   read -p "DESTRUCTIVELY OVERWRITING OUTPUT. Press any key to continue" -n 1 -r
   OVERWRITE_PARAMS="--overwrite-error-files"
fi

if [[ $DEBUG == "true" ]]
then
  RELEASE=""
fi

cargo build $RELEASE --bin rolandc_cli --bin roland_test_runner

if [[ $DEBUG == "true" ]];
then
   if [ $OSTYPE == "cygwin" ];
   then
      ./target/debug/roland_test_runner.exe tests/ --cli `cygpath -d --absolute ./target/debug/rolandc_cli.exe` $OVERWRITE_PARAMS
   else
      ./target/debug/roland_test_runner tests/ --cli `readlink --canonicalize ./target/debug/rolandc_cli` $OVERWRITE_PARAMS
   fi
else
   if [ $OSTYPE == "cygwin" ];
   then
      ./target/release/roland_test_runner.exe tests/ --cli `cygpath -d --absolute ./target/release/rolandc_cli.exe` $OVERWRITE_PARAMS
   else
      ./target/release/roland_test_runner tests/ --cli `readlink --canonicalize ./target/release/rolandc_cli` $OVERWRITE_PARAMS
   fi
fi
