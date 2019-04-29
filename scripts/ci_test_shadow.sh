#!/bin/sh

# Travis CI uses this script to test the Shadow library.

# Exit on any nonzero return code.
set -e

# Function for running the existing test and demo executables.
run_tests_and_demos() {
    # For commit builds, run the full Shadow demo and tests. For pull request builds,
    # run only the unit tests (credentials are not available for pull request builds).
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        ./bin/aws_iot_tests_shadow
        ./bin/aws_iot_demo_shadow -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$IOT_IDENTIFIER"
    else
        # Run only Shadow unit tests.
        ./bin/aws_iot_tests_shadow -n
    fi
}

# CMake compiler flags for building Shadow.
CMAKE_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_LOG_LEVEL_DEMO=IOT_LOG_INFO -DAWS_IOT_DEMO_SHADOW_UPDATE_PERIOD_MS=1 $COMPILER_OPTIONS"

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 aws_iot_tests_shadow aws_iot_demo_shadow

# Run tests and demos.
run_tests_and_demos

# Rebuild in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
make -j2 aws_iot_tests_shadow aws_iot_demo_shadow

# Run tests and demos in static memory mode.
run_tests_and_demos
