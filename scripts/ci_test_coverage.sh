#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.
# It does not run tests that require the network.

# Exit on any nonzero return code.
set -ev

# Query the AWS account ID.
AWS_ACCOUNT_ID=$(aws sts get-caller-identity --output text --query 'Account')

# Prefix of Job IDs used in the tests, set by the create_jobs function.
JOB_PREFIX=""

# Function to create Jobs to use in the tests.
create_jobs() {
    JOB_PREFIX=$IOT_IDENTIFIER-$(jot -r 1 1 100000)
    aws iot create-job \
        --job-id $JOB_PREFIX-1 \
        --targets arn:aws:iot:$AWS_DEFAULT_REGION:$AWS_ACCOUNT_ID:thing/$IOT_IDENTIFIER \
        --document '{"action":"print","message":"Hello world!"}'
    aws iot create-job \
        --job-id $JOB_PREFIX-2 \
        --targets arn:aws:iot:$AWS_DEFAULT_REGION:$AWS_ACCOUNT_ID:thing/$IOT_IDENTIFIER \
        --document '{"action":"print","message":"Hello world!"}'
}

# Function to delete Jobs and clean up the tests.
delete_jobs() {
    aws iot delete-job --job-id $JOB_PREFIX-1 --force
    aws iot delete-job --job-id $JOB_PREFIX-2 --force
}

# Build tests and demos against AWS IoT with coverage.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DAWS_IOT_TEST_JOBS_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_LOG_LEVEL_GLOBAL=IOT_LOG_DEBUG -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$IOT_IDENTIFIER\\\"\" -DIOT_TEST_COVERAGE=1 --coverage"
make -j2

# Run common tests with code coverage.
./output/bin/iot_tests_common

# Run MQTT tests against AWS IoT with code coverage.
./output/bin/iot_tests_mqtt

# Run Shadow tests with code coverage.
./output/bin/aws_iot_tests_shadow

# Run Jobs tests with code coverage.
create_jobs
trap "delete_jobs" EXIT
./output/bin/aws_iot_tests_jobs
delete_jobs
trap - EXIT

# Generate code coverage results, but only for files in libraries/.
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '*demo*' --output-file coverage.info
lcov --remove coverage.info '*ports*' --output-file coverage.info
lcov --remove coverage.info '*tests*' --output-file coverage.info
lcov --remove coverage.info '*third_party*' --output-file coverage.info

# Submit the code coverage results. Must be submitted from SDK root directory so
# Coveralls displays the correct paths.
cd ..
coveralls --lcov-file build/coverage.info
