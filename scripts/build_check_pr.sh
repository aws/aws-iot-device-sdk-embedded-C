#!/bin/sh

# Travis CI uses this script to check GitHub pull requests. It builds the
# demos and tests, then runs the demos and tests that require no credentials.

# Exit on any nonzero return code.
set -e

# Set Thing Name.
AWS_IOT_THING_NAME="$AWS_IOT_THING_NAME_PREFIX$CC"

# Create build directory.
mkdir -p build
cd build
rm -rf *

# Build tests and demos against Mosquitto broker with ThreadSanitizer.
cmake .. -DAWS_IOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DAWS_IOT_TEST_MQTT_MOSQUITTO=1 -DAWS_IOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -fsanitize=thread"
make

# Run MQTT tests and demos against Mosquitto.
./bin/aws_iot_tests_mqtt
./bin/aws_iot_demo_mqtt -h test.mosquitto.org -p 1883 -n

# Run the Shadow tests that do not require the network.
./bin/aws_iot_tests_shadow -n

# Rebuild in static memory mode.
rm -rf *
cmake .. -DAWS_IOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DAWS_IOT_TEST_MQTT_MOSQUITTO=1 -DAWS_IOT_STATIC_MEMORY_ONLY=1 -DAWS_IOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -fsanitize=thread"
make

# Run MQTT tests and no-network Shadow tests in static memory mode.
./bin/aws_iot_tests_mqtt
./bin/aws_iot_tests_shadow -n
