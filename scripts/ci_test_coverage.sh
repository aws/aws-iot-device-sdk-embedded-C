#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.
# It does not run tests that require the network.

# Exit on any nonzero return code.
set -e

# Function that generates code coverage report from the gcov files for a library. (it ignores all non-production code)
function generate_coverage() {
    if [ $# -ne 1 ]; then
        echo '"generate_coverage" requires input argument of coverage filename.'
        exit 1
    fi

    # Generate code coverage results, but only for files in libraries/.
    lcov --rc lcov_branch_coverage=1 --directory . --capture --output-file $1
    lcov --rc lcov_branch_coverage=1 --remove $1 '*demo*' --output-file $1
    lcov --rc lcov_branch_coverage=1 --remove $1 '*ports*' --output-file $1
    lcov --rc lcov_branch_coverage=1 --remove $1 '*test*' --output-file $1
    lcov --rc lcov_branch_coverage=1 --remove $1 '*third_party*' --output-file $1
}

# Overwrite the value of the COMPILER_OPTIONS variable to remove any thread sanitizer flags, and replace with coverage flags.
export COMPILER_OPTIONS="-DIOT_TEST_COVERAGE=1 --coverage -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG"

SCRIPTS_FOLDER_PATH=../scripts

# Run common tests with code coverage.
$SCRIPTS_FOLDER_PATH/ci_test_common.sh
generate_coverage common.info

# Run MQTT tests against AWS IoT with code coverage.
$SCRIPTS_FOLDER_PATH/ci_test_mqtt.sh
generate_coverage mqtt.info

# Run Shadow tests with code coverage.
$SCRIPTS_FOLDER_PATH/ci_test_shadow.sh
generate_coverage shadow.info

# Run Jobs tests with code coverage.
$SCRIPTS_FOLDER_PATH/ci_test_jobs.sh
generate_coverage jobs.info

# Run Provisioning tests with code coverage.
$SCRIPTS_FOLDER_PATH/ci_test_provisioning.sh
generate_coverage provisioning.info

# Combine the coverage files of all libraries into a single master coverage file.
lcov --rc lcov_branch_coverage=1 \
     --add-tracefile common.info \
     --add-tracefile mqtt.info \
     --add-tracefile shadow.info \
     --add-tracefile jobs.info \
     --add-tracefile provisioning.info \
     --output-file coverage.info
