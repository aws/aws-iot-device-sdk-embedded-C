#!/bin/sh

# Travis CI uses this script to test the Onboarding library.

# Exit on any nonzero return code.
set -e

TEST_OPTIONS="-n"

# CMake build configuration..
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL

make -j2 aws_iot_tests_onboarding
./bin/aws_iot_tests_onboarding $TEST_OPTIONS

# Rebuild and run tests in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DIOT_STATIC_MEMORY_ONLY=1"

make -j2 aws_iot_tests_onboarding
./bin/aws_iot_tests_onboarding $TEST_OPTIONS

