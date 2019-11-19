#!/bin/sh

# Travis CI uses this script to test the Jobs library.

# Exit on any nonzero return code.
set -e

# Query the AWS account ID.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    AWS_ACCOUNT_ID=$(aws sts get-caller-identity --output text --query 'Account')
fi

# Prefix of Job IDs used in the tests, set by the create_jobs function.
JOB_PREFIX=""

# Function for running the existing test executables.
run_tests() {
    # For commit builds, run the full Jobs tests. For pull request builds,
    # run only the unit tests (credentials are not available for pull request builds).
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        ./output/bin/aws_iot_tests_jobs
    else
        # Run only Jobs unit tests.
        ./output/bin/aws_iot_tests_jobs -n
    fi
}

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

# CMake compiler flags for building Jobs.
CMAKE_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_JOBS_THING_NAME=\"\\\"$IOT_IDENTIFIER\\\"\" $COMPILER_OPTIONS"

# Build executables.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS"
make -j2 aws_iot_tests_jobs

# Run tests.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then create_jobs; fi
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then trap "delete_jobs" EXIT; fi
run_tests
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then delete_jobs; fi

# Rebuild in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$CMAKE_FLAGS -DIOT_STATIC_MEMORY_ONLY=1"
make -j2 aws_iot_tests_jobs

# Run tests in static memory mode.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then create_jobs; fi
run_tests
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then delete_jobs; fi

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then trap - EXIT; fi
