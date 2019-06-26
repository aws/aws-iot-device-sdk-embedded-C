#!/bin/sh

# Travis CI uses this script to test the Jobs library.

# Exit on any nonzero return code.
set -e

# CMake compiler flags for building Jobs.
CMAKE_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_JOBS_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" $COMPILER_OPTIONS"

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 aws_iot_tests_jobs

# Run tests.
./bin/aws_iot_tests_jobs

# Rebuild in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
make -j2 aws_iot_tests_jobs

# Run tests in static memory mode.
./bin/aws_iot_tests_jobs
