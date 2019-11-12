#!/bin/sh

# Travis CI uses this script to test the Onboarding library.

# Exit on any nonzero return code.
set -exu

AWS_ACCOUNT_ID=""

# Query the AWS account ID.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    AWS_ACCOUNT_ID=$(aws sts get-caller-identity --output text --query 'Account')
fi

# Function for running the existing test executables.
run_tests() {
    # For commit builds, run the full Onboarding tests. For pull request builds,
    # run only the unit tests (credentials are not available for pull request builds).
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        ./bin/aws_iot_tests_onboarding
    else
        # Run only Onboarding unit tests.
        ./bin/aws_iot_tests_onboarding -n
    fi
}

# Hard-coded with template present in CI account.
# TODO - Update with creating template (using Aws CLI) for system test setup. 
TEMPLATE_NAME="CI_TEST_TEMPLATE"

PROVISION_PARAMETERS="{ \
    { \
        .pParameterKey = \"\\\"DeviceLocation\\\"\", \
        .parameterKeyLength = sizeof( \"\\\"DeviceLocation\\\"\" ) - 1, \
        .pParameterValue = \"\\\"Seattle\\\"\", \
        .parameterValueLength = sizeof(\"\\\"Seattle\\\"\" ) - 1 \
    } \
}"

AWS_IOT_CREDENTIAL_DEFINES=""
# Function that creates a compiler flags string for network and credentials configuration of the tests.
configure_credentials() {

    mkdir credentials

    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
    then
        wget https://www.amazontrust.com/repository/AmazonRootCA1.pem -O credentials/AmazonRootCA1.pem; 
    fi

    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
    then
        echo -e $AWS_IOT_CLIENT_CERT > credentials/clientCert.pem;
    fi

    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
    then
        echo -e $AWS_IOT_PRIVATE_KEY > credentials/privateKey.pem; 
    fi


    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
    then 
        AWS_IOT_CREDENTIAL_DEFINES="-DIOT_TEST_SERVER=\"\\\"$AWS_IOT_ENDPOINT\\\"\" -DIOT_TEST_PORT=443 -DIOT_TEST_ROOT_CA=\"\\\"credentials/AmazonRootCA1.pem\\\"\" -DIOT_TEST_CLIENT_CERT=\"\\\"credentials/clientCert.pem\\\"\" -DIOT_TEST_PRIVATE_KEY=\"\\\"credentials/privateKey.pem\\\"\""; 
    fi
}

configure_credentials

# Create unique certificate on the AWS IoT account that can be used as the certificate to provision
# the system/integration tests with. We will just save the certificate ID to use in the tests.
CERTIFICATE_ID=$(aws iot create-keys-and-certificate \
    --endpoint https://gamma.us-east-1.iot.amazonaws.com \
    --no-set-as-active | \
        grep certificateId | \
            cut -d ':' -f2 | \
                tr -d ,)

COMMON_CMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_ONBOARDING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_ONBOARDING_TEMPLATE_PARAMETERS=\"$PROVISION_PARAMETERS\" -DAWS_IOT_TEST_PROVISIONING_CERTIFICATE_ID=\"\\\"$CERTIFICATE_ID\\\"\""

# CMake build configuration without static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$COMMON_CMAKE_C_FLAGS"
#cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DAWS_IOT_ONBOARDING_TEMPLATE_NAME=$TEMPLATE_NAME"

# Build tests.
make -j2 aws_iot_tests_onboarding

# Run tests in no static memory mode.
run_tests

# Rebuild and run tests in static memory mode.
#cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DIOT_STATIC_MEMORY_ONLY=1 $COMMON_CMAKE_C_FLAGS"

# Run tests in no static memory mode.
#run_tests

