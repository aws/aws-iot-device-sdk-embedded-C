#!/bin/sh

# Travis CI uses this script to test the Shadow library.

# Exit on any nonzero return code.
set -e

# Function for running the existing test and demo executables.
run_tests_and_demos() {
    # For commit builds, run the full Shadow demo and tests. For pull request builds,
    # run only the unit tests (credentials are not available for pull request builds).
    # Sleep for 1.1 seconds between the runs to respect AWS service limits.
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        ./output/bin/aws_iot_tests_shadow
        sleep 1.1
        ./output/bin/aws_iot_demo_shadow
    else
        # Run only Shadow unit tests.
        ./output/bin/aws_iot_tests_shadow -n
    fi
}

# CMake compiler flags for building Shadow.
CMAKE_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DAWS_IOT_DEMO_SHADOW_UPDATE_PERIOD_MS=1 $COMPILER_OPTIONS"

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 aws_iot_tests_shadow aws_iot_demo_shadow

# Run tests and demos.
run_tests_and_demos

if [ "$RUN_TEST" != "coverage" ]; then
    # Rebuild in static memory mode.
    cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
    make -j2 aws_iot_tests_shadow aws_iot_demo_shadow

    # Run tests and demos in static memory mode.
    run_tests_and_demos
fi