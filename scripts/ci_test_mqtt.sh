#!/bin/sh

# Travis CI uses this script to test the MQTT library.

# Exit on any nonzero return code.
set -e

CMAKE_FLAGS="-DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" "

# For pull request builds, run against test.mosquitto.org. Otherwise, run against AWS IoT.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    CMAKE_FLAGS+="$AWS_IOT_CREDENTIAL_DEFINES $COMPILER_OPTIONS"
    DEMO_OPTIONS="-i $IOT_IDENTIFIER"
elif [ "$TRAVIS_OS_NAME" = "windows" ]; then
    CMAKE_FLAGS+=$COMPILER_OPTIONS
    DEMO_OPTIONS="-n -i $IOT_IDENTIFIER"
else
    CMAKE_FLAGS+="-DIOT_TEST_MQTT_MOSQUITTO=1 -DIOT_TEST_SERVER=\\\"localhost\\\" $COMPILER_OPTIONS"
    DEMO_OPTIONS="-n -i $IOT_IDENTIFIER -u -h localhost -p 1883"
fi

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
if [ "$TRAVIS_OS_NAME" != "windows" ]; then
    make -j2 iot_tests_mqtt iot_demo_mqtt
else
    MSBuild.exe tests/mqtt/iot_tests_mqtt.vcxproj -m -clp:summary -verbosity:minimal
    MSBuild.exe demos/app/iot_demo_mqtt.vcxproj -m -clp:summary -verbosity:minimal
    mv ./bin/Debug/* ./bin/
fi

# Run tests and demos.
./bin/iot_tests_mqtt
./bin/iot_demo_mqtt $DEMO_OPTIONS

# Rebuild in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
if [ "$TRAVIS_OS_NAME" != "windows" ]; then
    make -j2 iot_tests_mqtt
else
    MSBuild.exe tests/mqtt/iot_tests_mqtt.vcxproj -m -clp:summary -verbosity:minimal
    mv ./bin/Debug/* ./bin/
fi

# Run tests in static memory mode.
./bin/iot_tests_mqtt
