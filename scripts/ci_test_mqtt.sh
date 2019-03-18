#!/bin/sh

# Travis CI uses this script to test the MQTT library.

# Exit on any nonzero return code.
set -e

# Function for running the existing test and demo executables.
run_tests_and_demos() {
    # Run MQTT tests.
    ./bin/iot_tests_mqtt

    # Run MQTT demo with appropriate arguments.
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        # Run against AWS IoT.
        ./bin/iot_demo_mqtt -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$IOT_IDENTIFIER"
    else
        # Run against Mosquitto.
        ./bin/iot_demo_mqtt -h test.mosquitto.org -p 1883 -n
    fi
}

# For pull request builds, run against test.mosquitto.org. Otherwise, run against AWS IoT.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    CMAKE_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_LOG_LEVEL_DEMO=IOT_LOG_INFO -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" $COMPILER_OPTIONS"
else
    CMAKE_FLAGS="-DIOT_TEST_MQTT_MOSQUITTO=1 $COMPILER_OPTIONS"
fi

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2

# Run tests and demos.
run_tests_and_demos

# Rebuild in static memory mode.
rm -rf *
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
make -j2

# Run tests in static memory mode.
./bin/iot_tests_mqtt
