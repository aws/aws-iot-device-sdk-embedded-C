#!/bin/sh

# Travis CI uses this script to test the Onboarding library.

# Exit on any nonzero return code.
set -exu

TRAVIS_PULL_REQUEST=false

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

TEMPLATE_NAME="CI_TEST_TEMPLATE"

# Function to setup template for the integration tests.
create_provisioning_template() {
    # Delete all existing templates in the account to start afresh.
    aws iot delete-provisioning-template \
        --endpoint https://gamma.us-east-1.iot.amazonaws.com \
        --template-name $TEMPLATE_NAME | echo true
    
    # Add a single provisioning template to test with.
    aws iot create-provisioning-template \
        --endpoint https://gamma.us-east-1.iot.amazonaws.com \
        --template-name $TEMPLATE_NAME \
        --provisioning-role-arn arn:aws:iam::$AWS_ACCOUNT_ID:role/Admin \
        --template-body  "{ \"Resources\": {}}" \
        --enabled 
}

# Function to delete the template from the account
delete_provisioning_template() {
    aws iot delete-provisioning-template \
        --endpoint https://beta.us-east-1.iot.amazonaws.com \
        --template-name $TEMPLATE_NAME
}

#create_provisioning_template
# delete_provisioning_template

PROVISION_PARAMETERS="{ \
    { \
        .pParameterKey = \"\\\"DeviceLocation\\\"\", \
        .parameterKeyLength = sizeof( \"\\\"DeviceLocation\\\"\" ) - 1, \
        .pParameterValue = \"\\\"Seattle\\\"\", \
        .parameterValueLength = sizeof(\"\\\"Seattle\\\"\" ) - 1 \
    } \
}"


if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
then wget https://www.amazontrust.com/repository/AmazonRootCA1.pem -O credentials/AmazonRootCA1.pem; 
fi

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
then echo -e $AWS_IOT_CLIENT_CERT > credentials/clientCert.pem;
fi

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
then echo -e $AWS_IOT_PRIVATE_KEY > credentials/privateKey.pem; 
fi

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; 
then export AWS_IOT_CREDENTIAL_DEFINES=-DIOT_TEST_SERVER=\\\"\\\\\\\"$AWS_IOT_ENDPOINT\\\\\\\"\\\" -DIOT_TEST_PORT=443 -DIOT_TEST_ROOT_CA=\\\"\\\\\\\"../credentials/AmazonRootCA1.pem\\\\\\\"\\\" -DIOT_TEST_CLIENT_CERT=\\\"\\\\\\\"../credentials/clientCert.pem\\\\\\\"\\\" -DIOT_TEST_PRIVATE_KEY=\\\"\\\\\\\"../credentials/privateKey.pem\\\\\\\"\\\"; 
fi

COMMON_CMAKE_FLAGS="\"$AWS_IOT_CREDENTIAL_DEFINE\" -DAWS_IOT_TEST_ONBOARDING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_ONBOARDING_TEMPLATE_PARAMETERS=\"$PROVISION_PARAMETERS\""

# CMake build configuration without static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$COMMON_CMAKE_FLAGS"
#cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DAWS_IOT_ONBOARDING_TEMPLATE_NAME=$TEMPLATE_NAME"

# Build tests.
make -j2 aws_iot_tests_onboarding

# Setup test
create_provisioning_template

# Run tests in no static memory mode.
run_tests

# Rebuild and run tests in static memory mode.
 cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DIOT_STATIC_MEMORY_ONLY=1 $COMMON_CMAKE_FLAGS"

# Run tests in no static memory mode.
run_tests

# Cleanup test.
delete_provisioning_template
