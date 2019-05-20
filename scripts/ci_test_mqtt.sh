#!/bin/sh

# Travis CI uses this script to test the MQTT library.

# Exit on any nonzero return code.
set -e

CMAKE_FLAGS="-DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" "

# For pull request builds, run against test.mosquitto.org. Otherwise, run against AWS IoT.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    CMAKE_FLAGS+="$AWS_IOT_CREDENTIAL_DEFINES $COMPILER_OPTIONS"
else
    CMAKE_FLAGS+="-DIOT_TEST_MQTT_MOSQUITTO=1 $COMPILER_OPTIONS"
    DEMO_OPTIONS="-n"
fi

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 iot_tests_mqtt iot_demo_mqtt

# Run tests and demos.
./bin/iot_tests_mqtt
./bin/iot_demo_mqtt $DEMO_OPTIONS

# Rebuild in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
make -j2 iot_tests_mqtt

# Run tests in static memory mode.
./bin/iot_tests_mqtt
