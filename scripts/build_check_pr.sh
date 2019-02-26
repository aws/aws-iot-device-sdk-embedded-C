#!/bin/sh

# Travis CI uses this script to check GitHub pull requests. It builds the
# demos and tests, then runs the demos and tests that require no credentials.

# Exit on any nonzero return code.
set -e

# Additional options for compilation.
COMPILER_OPTIONS="-Wall -Wextra -fsanitize=thread"

# Create build directory.
mkdir -p build
cd build
rm -rf *

# Build tests and demos against Mosquitto broker with ThreadSanitizer.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DIOT_TEST_MQTT_MOSQUITTO=1 $COMPILER_OPTIONS"
make

# Run common tests (no network required).
./bin/iot_tests_common

# Run MQTT tests and demos against Mosquitto.
./bin/iot_tests_mqtt
./bin/iot_demo_mqtt -h test.mosquitto.org -p 1883 -n

# Run the Shadow tests that do not require the network.
./bin/aws_iot_tests_shadow -n

# Run serializer tests
./bin/iot_tests_serializer

# Rebuild in static memory mode.
rm -rf *
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DIOT_TEST_MQTT_MOSQUITTO=1 -DIOT_STATIC_MEMORY_ONLY=1 $COMPILER_OPTIONS"
make

# Run common tests in static memory mode (no network required).
./bin/iot_tests_common

# Run MQTT tests and no-network Shadow tests in static memory mode.
./bin/iot_tests_mqtt
./bin/aws_iot_tests_shadow -n

# Run serializer tests
./bin/iot_tests_serializer
