#!/bin/sh

# Travis CI uses this script to test the MQTT library.

# Exit on any nonzero return code.
set -e

CMAKE_FLAGS="-DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" $COMPILER_OPTIONS"
TEST_OPTIONS=""

DEMO_OPTIONS="-i $IOT_IDENTIFIER"

# For pull request builds on Linux, run against a local Mosquitto broker.
#
# On macOS and Windows, a local Mosquitto broker is not available. Only tests
# that do not use the network should run on these platforms.
#
# For commit builds all platforms will test against AWS IoT.
if [ "$TRAVIS_PULL_REQUEST" != "false" ]; then
    if [ "$TRAVIS_OS_NAME" = "linux" ]; then
        # Set the flags and options for a local Mosquitto broker on Linux.
        CMAKE_FLAGS+=" -DIOT_TEST_MQTT_MOSQUITTO=1 -DIOT_TEST_SERVER=\\\"localhost\\\""
        DEMO_OPTIONS+=" -n -u -h localhost -p 1883"
    else
        # Specify that the tests should not use the network on macOS and Windows.
        TEST_OPTIONS="-n"
    fi
else
    # Set credentials for AWS IoT.
    CMAKE_FLAGS+=" $AWS_IOT_CREDENTIAL_DEFINES"
fi

# Build and run executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS"

if [ "$TRAVIS_OS_NAME" = "windows" ]; then
    MSBuild.exe libraries/standard/mqtt/iot_tests_mqtt.vcxproj -m -clp:summary -verbosity:minimal
    MSBuild.exe demos/iot_demo_mqtt.vcxproj -m -clp:summary -verbosity:minimal

    ./bin/Debug/iot_tests_mqtt.exe $TEST_OPTIONS
else
    make -j2 iot_tests_mqtt iot_demo_mqtt

    ./bin/iot_tests_mqtt $TEST_OPTIONS

    if [ "$TRAVIS_OS_NAME" = "linux" ]; then
        ./bin/iot_demo_mqtt $DEMO_OPTIONS
    fi
fi

# Rebuild and run tests in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"

if [ "$TRAVIS_OS_NAME" = "windows" ]; then
    MSBuild.exe libraries/standard/mqtt/iot_tests_mqtt.vcxproj -m -clp:summary -verbosity:minimal
    MSBuild.exe demos/iot_demo_mqtt.vcxproj -m -clp:summary -verbosity:minimal

    ./bin/Debug/iot_tests_mqtt.exe $TEST_OPTIONS
else
    make -j2 iot_tests_mqtt iot_demo_mqtt

    ./bin/iot_tests_mqtt $TEST_OPTIONS
fi
