#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.

# Exit on any nonzero return code.
set -ev

# Build tests and demos against AWS IoT with coverage.
cmake .. -DCMAKE_C_COMPILER=gcc -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$IOT_IDENTIFIER\\\"\" -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_COVERAGE=1 --coverage"
make -j2

# Run common tests with code coverage.
./bin/iot_tests_common

# Run MQTT tests and demo against AWS IoT with code coverage.
./bin/iot_tests_mqtt
./bin/iot_demo_mqtt -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$IOT_IDENTIFIER"

# Run Shadow tests and demo with code coverage.
./bin/aws_iot_tests_shadow
./bin/aws_iot_demo_shadow -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$IOT_IDENTIFIER"

# Generate code coverage results, excluding Unity test framework, demo files, tests files, and third party files.
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '*unity*' --output-file coverage.info
lcov --remove coverage.info '*demo*' --output-file coverage.info
lcov --remove coverage.info '*tests*' --output-file coverage.info
lcov --remove coverage.info '*third_party*' --output-file coverage.info

# Submit the code coverage results. Must be submitted from SDK root directory so
# Coveralls displays the correct paths.
cd ..
coveralls --lcov-file build/coverage.info
