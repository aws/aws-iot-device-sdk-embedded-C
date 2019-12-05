#!/bin/sh

# Travis CI uses this script to test the MQTT library.

# Exit on any nonzero return code.
set -e

CMAKE_NON_CREDENTIAL_FLAGS="-DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" $COMPILER_OPTIONS"
TEST_OPTIONS=""

DEMO_OPTIONS="-i $IOT_IDENTIFIER"

# For pull request builds on Linux, run against a local Mosquitto broker.
#
# For commit builds all platforms will test against AWS IoT.
if [ "$TRAVIS_PULL_REQUEST" != "false" ]; then
    if [ "$TRAVIS_OS_NAME" = "linux" ]; then
        # Set the flags and options for a local Mosquitto broker on Linux.
        CMAKE_CREDENTIAL_FLAGS+=" -DIOT_TEST_MQTT_MOSQUITTO=1 -DIOT_TEST_SERVER=\\\"localhost\\\""
        DEMO_OPTIONS+=" -n -u -h localhost -p 1883"
    fi
else
    # Set credentials for AWS IoT.
    CMAKE_CREDENTIAL_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES"
fi

CMAKE_FLAGS="$CMAKE_NON_CREDENTIAL_FLAGS $CMAKE_CREDENTIAL_FLAGS"

# Build and run executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS"

make -j2 iot_tests_mqtt iot_demo_mqtt

./output/bin/iot_tests_mqtt $TEST_OPTIONS

# Don't reconfigure CMake if script is invoked for coverage build.
if [ "$RUN_TEST" != "coverage" ]; then
    if [ "$TRAVIS_OS_NAME" = "linux" ]; then
        ./output/bin/iot_demo_mqtt $DEMO_OPTIONS
    fi

    # Rebuild and run tests in static memory mode.
    cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"

    make -j2 iot_tests_mqtt iot_demo_mqtt

    ./output/bin/iot_tests_mqtt $TEST_OPTIONS
fi
