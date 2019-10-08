#!/bin/sh

# Travis CI uses this script to test various build configurations.

# Exit on any nonzero return code.
set -e

# Treat warnings as errors.
if [ "$TRAVIS_COMPILER" = "clang" ]; then
    COMPILER_OPTIONS+=" -Werror"
elif [ "$TRAVIS_COMPILER" = "msvc" ]; then
    COMPILER_OPTIONS+=" /W4 /Wd4200 /WX"
fi

# Build demos.
cmake .. -DCMAKE_C_FLAGS="$COMPILER_OPTIONS"

if [ "$TRAVIS_OS_NAME" = "windows" ]; then
    MSBuild.exe ALL_BUILD.vcxproj -m -clp:summary -verbosity:minimal
else
    make -j2
fi

# Build tests. Enable all logging.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_C_FLAGS="$COMPILER_OPTIONS -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG"

if [ "$TRAVIS_OS_NAME" = "windows" ]; then
    MSBuild.exe ALL_BUILD.vcxproj -m -clp:summary -verbosity:minimal
else
    make -j2
fi
