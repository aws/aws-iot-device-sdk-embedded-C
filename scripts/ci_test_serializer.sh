#!/bin/sh

# Travis CI uses this script to test the serializer library.

# Exit on any nonzero return code.
set -e

# CMake compiler flags for building common libraries.
CMAKE_FLAGS="$COMPILER_OPTIONS"

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 iot_tests_serializer

# Run common tests.
./output/bin/iot_tests_common

# Don't reconfigure CMake if script is invoked for coverage build.
if [ "$RUN_TEST" != "coverage" ]; then 
    # Rebuild in static memory mode.
    cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
    make -j2 iot_tests_serializer

    # Run common tests in static memory mode.
    ./output/bin/iot_tests_serializer
fi