#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.

# Exit on any nonzero return code.
set -e

# Set Thing Name.
AWS_IOT_THING_NAME="$AWS_IOT_THING_NAME_PREFIX$CC"

# Delete everything in the build directory.
mkdir -p build
cd build
rm -rf *

# Build tests and demos against AWS IoT with gcov.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DIOT_TEST_SERVER=\"\\\"$AWS_IOT_ENDPOINT\\\"\" -DIOT_TEST_PORT=443 -DIOT_TEST_ROOT_CA=\"\\\"../credentials/AmazonRootCA1.pem\\\"\" -DIOT_TEST_CLIENT_CERT=\"\\\"../credentials/clientCert.pem\\\"\" -DIOT_TEST_PRIVATE_KEY=\"\\\"../credentials/privateKey.pem\\\"\" -DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_TEST_COVERAGE=1 --coverage"
make

# Run Common tests with code coverage.
./bin/iot_tests_mqtt 2&> /dev/null

# Run MQTT tests and demo against AWS IoT with code coverage.
./bin/iot_tests_mqtt 2&> /dev/null
./bin/iot_demo_mqtt -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME" 2&> /dev/null

# Run Shadow tests and demo with code coverage.
./bin/aws_iot_tests_shadow 2&> /dev/null
./bin/aws_iot_demo_shadow -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME" 2&> /dev/null

# Run Defender tests with code coverage.
./bin/aws_iot_tests_defender 2&> /dev/null

# Generate code coverage results, excluding Unity test framework, demo files, and tests files.
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '*unity*' --output-file coverage.info
lcov --remove coverage.info '*demo*' --output-file coverage.info
lcov --remove coverage.info '*tests*' --output-file coverage.info

# Submit the code coverage results.
cd ..
coveralls --lcov-file build/coverage.info
