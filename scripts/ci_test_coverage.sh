#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.
# It does not run tests that require the network.

# Exit on any nonzero return code.
set -ev

# Build tests and demos against AWS IoT with coverage.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DAWS_IOT_TEST_JOBS_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_COVERAGE=1 --coverage"
make -j2

# Run common tests with code coverage.
./bin/iot_tests_common

# Run MQTT tests against AWS IoT with code coverage.
./bin/iot_tests_mqtt

# Run Shadow tests with code coverage.
./bin/aws_iot_tests_shadow

# Run Jobs tests with code coverage.
./bin/aws_iot_tests_jobs

# Generate code coverage results, but only for files in lib/.
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '*demo*' --output-file coverage.info
lcov --remove coverage.info '*platform*' --output-file coverage.info
lcov --remove coverage.info '*tests*' --output-file coverage.info
lcov --remove coverage.info '*third_party*' --output-file coverage.info

# Submit the code coverage results. Must be submitted from SDK root directory so
# Coveralls displays the correct paths.
cd ..
coveralls --lcov-file build/coverage.info
