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
    lcov --directory . --capture --output-file $1
    lcov --remove $1 '*demo*' --output-file $1
    lcov --remove $1 '*ports*' --output-file $1
    lcov --remove $1 '*tests*' --output-file $1
    lcov --remove $1 '*third_party*' --output-file $1
}

# Overwrite the value of the COMPILER_OPTIONS varirable to remove any thread sanitizer flags, and replace with coverage flags.
export COMPILER_OPTIONS="-DIOT_TEST_COVERAGE=1 --coverage"

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

# Combine the coverage files of all libraries into a single master coverage file.
lcov --add-tracefile common.info \
     --add-tracefile mqtt.info \
     --add-tracefile shadow.info \
     --add-tracefile jobs.info \
     --output-file coverage.info

# Submit the code coverage results. Must be submitted from SDK root directory so
# Coveralls displays the correct paths.
cd ..
coveralls --lcov-file build/coverage.info
