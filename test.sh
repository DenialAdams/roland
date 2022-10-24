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

cargo run $RELEASE --bin roland_test_runner -- tests/ $OVERWRITE_PARAMS
