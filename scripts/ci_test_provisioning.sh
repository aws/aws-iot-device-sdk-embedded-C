#!/bin/sh

# Travis CI uses this script to test the Provisioning library.

# Exit on any nonzero return code.
set -exu

AWS_ACCOUNT_ID=""

# Query the AWS account ID.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    AWS_ACCOUNT_ID=$(aws sts get-caller-identity --output text --query 'Account')
fi

# Function for running the existing test executables.
run_tests() {
    # For commit builds, run the full Provisioning tests. For pull request builds,
    # run only the unit tests (credentials are not available for pull request builds).
    if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
        ./output/bin/aws_iot_tests_provisioning
    else
        # Run only Provisioning unit tests.
        ./output/bin/aws_iot_tests_provisioning -n
    fi
}

# Hard-coded with template present in CI account.
# TODO - Update with creating template (using Aws CLI) for system test setup. 
TEMPLATE_NAME="CI_TEST_TEMPLATE"

# Parameters to inject in the syste/integration test to pass as provisioning parameters.
SERIAL_NUMBER_DEVICE_CONTEXT="1122334455667788"
PROVISIONING_PARAMETERS="{ \
    { \
        .pParameterKey = \"\\\"DeviceLocation\\\"\", \
        .parameterKeyLength = sizeof( \"\\\"DeviceLocation\\\"\" ) - 1, \
        .pParameterValue = \"\\\"Seattle\\\"\", \
        .parameterValueLength = sizeof(\"\\\"Seattle\\\"\" ) - 1 \
    }, \
    { \
        .pParameterKey = \"\\\"SerialNumber\\\"\", \
        .parameterKeyLength = sizeof( \"\\\"SerialNumber\\\"\" ) - 1, \
        .pParameterValue = \"\\\"$SERIAL_NUMBER_DEVICE_CONTEXT\\\"\", \
        .parameterValueLength = sizeof(\"\\\"$SERIAL_NUMBER_DEVICE_CONTEXT\\\"\" ) - 1 \
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

COMMON_CMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS=\"$PROVISIONING_PARAMETERS\""

# CMake build configuration without static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$COMMON_CMAKE_C_FLAGS"

# Build tests.
make -j2 aws_iot_tests_provisioning

# Run tests in no static memory mode.
run_tests

# Rebuild and run tests in static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DIOT_STATIC_MEMORY_ONLY=1 $COMMON_CMAKE_C_FLAGS"

# Build tests.
make -j2 aws_iot_tests_provisioning

# Run tests in no static memory mode.
run_tests

# Cleanup the created resources created by the integration tests on the CI AWS IoT account.
# (Resources include Thing resource, its attached certificates and their policies)
# (First, we will install a json parser utility, jq)
apt-get install -y jq

# Iterate over all the principals/certificates attached to the Thing resource (created by the integration test)
# and delete the certificates.
aws iot list-thing-principals \
    --endpoint $AWS_CLI_CI_ENDPOINT \
    --region $AWS_PROVISIONING_REGION \
    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT | \
        grep arn | tr -d \",' ' | 
            while read -r CERTIFICATE_ARN
            do
                # Detach the principal from the Thing resource.
                aws iot detach-thing-principal \
                    --endpoint $AWS_CLI_CI_ENDPOINT \
                    --region $AWS_PROVISIONING_REGION \
                    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT \
                    --principal $CERTIFICATE_ARN

                CERTIFICATE_ID=$(echo $CERTIFICATE_ARN | cut -d '/' -f2)

                aws iot update-certificate \
                    --endpoint $AWS_CLI_CI_ENDPOINT \
                    --region $AWS_PROVISIONING_REGION \
                    --certificate-id $CERTIFICATE_ID \
                    --new-status INACTIVE

                aws iot delete-certificate \
                    --endpoint $AWS_CLI_CI_ENDPOINT \
                    --region $AWS_PROVISIONING_REGION \
                    --certificate-id $CERTIFICATE_ID \
                    --force-delete
            done
aws iot delete-thing \
    --endpoint $AWS_CLI_CI_ENDPOINT \
    --region $AWS_PROVISIONING_REGION \
    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT

# Make best effort to delete any inactive certificate that may have been created by the integration tests.
aws iot list-certificates \
    --endpoint https://gamma.us-east-1.iot.amazonaws.com \
    --region $AWS_PROVISIONING_REGION | \
        jq -c '.certificates[] | select(.status | contains("INACTIVE")) | .certificateArn' | \
            tr -d \" | \
                while read -r cert_arn 
                do 
                    CERTIFICATE_ID=$(echo $cert_arn | cut -d '/' -f2)
                    # Attempt to delete the certificate (and ignore any errors that come with 
                    # the deletion request).
                    aws iot delete-certificate \
                        --endpoint https://gamma.us-east-1.iot.amazonaws.com \
                        --region $AWS_PROVISIONING_REGION \
                        --certificate-id $CERTIFICATE_ID \
                        --force-delete | \
                            echo true
                done