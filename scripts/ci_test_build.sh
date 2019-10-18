#!/bin/sh

# Travis CI uses this script to test various build configurations.

# Exit on any nonzero return code.
set -e

# Treat warnings as errors.
if [ "$TRAVIS_COMPILER" = "clang" ]; then
    COMPILER_OPTIONS+=" -Werror"
fi

# Build demos.
cmake .. -DCMAKE_C_FLAGS="$COMPILER_OPTIONS"
make -j2

# Build tests. Enable all logging.
rm -rf *
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_C_FLAGS="$COMPILER_OPTIONS -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG"
make -j2
