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

TEMPLATE_NAME="CI_SYSTEM_TEST_TEMPLATE"
PROVISIONING_ROLE_NAME="CI_SYSTEM_TEST_ROLE"

# Sets up all resources (Provisioning role, Fleet Provisioning template) on the AWS IoT account for running integration tests.
setup() {
    # Delete all existing templates in the account to start afresh.
    aws iot delete-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME | echo true
    
    # Create a provisioning role.
    aws iam create-role \
        --role-name $PROVISIONING_ROLE_NAME \
        --assume-role-policy-document '{"Version":"2012-10-17","Statement":[{"Action":"sts:AssumeRole","Effect":"Allow","Principal":{"Service":"iot.amazonaws.com"}}]}'
    aws iam attach-role-policy \
        --role-name $PROVISIONING_ROLE_NAME \
        --policy-arn arn:aws:iam::aws:policy/service-role/AWSIoTThingsRegistration

    # Add a single provisioning template to test with.
    aws iot create-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME \
        --provisioning-role-arn arn:aws:iam::$AWS_ACCOUNT_ID:role/$PROVISIONING_ROLE_NAME \
        --template-body  "{\"Parameters\":{\"DeviceLocation\":{\"Type\":\"String\"},\"AWS::IoT::Certificate::Id\":{\"Type\":\"String\"},\"SerialNumber\":{\"Type\":\"String\"}},\"Mappings\":{\"LocationTable\":{\"Seattle\":{\"LocationUrl\":\"https://example.aws\"}}},\"Resources\":{\"thing\":{\"Type\":\"AWS::IoT::Thing\",\"Properties\":{\"ThingName\":{\"Fn::Join\":[\"\",[\"ThingPrefix_\",{\"Ref\":\"SerialNumber\"}]]},\"AttributePayload\":{\"version\":\"v1\",\"serialNumber\":\"serialNumber\"}},\"OverrideSettings\":{\"AttributePayload\":\"MERGE\",\"ThingTypeName\":\"REPLACE\",\"ThingGroups\":\"DO_NOTHING\"}},\"certificate\":{\"Type\":\"AWS::IoT::Certificate\",\"Properties\":{\"CertificateId\":{\"Ref\":\"AWS::IoT::Certificate::Id\"},\"Status\":\"Active\"},\"OverrideSettings\":{\"Status\":\"REPLACE\"}},\"policy\":{\"Type\":\"AWS::IoT::Policy\",\"Properties\":{\"PolicyDocument\":{\"Version\":\"2012-10-17\",\"Statement\":[{\"Effect\":\"Allow\",\"Action\":[\"iot:Connect\",\"iot:Subscribe\",\"iot:Publish\",\"iot:Receive\"],\"Resource\":\"*\"}]}}}},\"DeviceConfiguration\":{\"FallbackUrl\":\"https://www.example.com/test-site\",\"LocationUrl\":{\"Fn::FindInMap\":[\"LocationTable\",{\"Ref\":\"DeviceLocation\"},\"LocationUrl\"]}}}" \
        --enabled 
}

# Removes all resources (Provisioning role, Fleet Provisioning template) that were created for integration tests in the AWS IoT account.
teardown() {
    # Delete Provisioning role.
    aws iam detach-role-policy \
        --role-name $PROVISIONING_ROLE_NAME \
        --policy-arn arn:aws:iam::aws:policy/service-role/AWSIoTThingsRegistration
    aws iam delete-role \
        --role-name $PROVISIONING_ROLE_NAME

    # Delete Fleet Provisioning Template.
    aws iot delete-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME
}

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

# Setup the AWS IoT account for integration tests.
setup

configure_credentials

COMMON_CMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS=\"$PROVISIONING_PARAMETERS\""

# CMake build configuration without static memory mode.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="$COMMON_CMAKE_C_FLAGS"

# Build tests.
make -j2 aws_iot_tests_provisioning

# Run tests in no static memory mode.
run_tests

# Rebuild and run tests in static memory mode. Specify a buffer size to accommodate for credentials.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DIOT_NETWORK_USE_OPENSSL=$IOT_NETWORK_USE_OPENSSL -DCMAKE_C_FLAGS="-DIOT_STATIC_MEMORY_ONLY=1 -DIOT_MESSAGE_BUFFER_SIZE=4096 $COMMON_CMAKE_C_FLAGS"

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
    --region $AWS_PROVISIONING_REGION \
    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT | \
        grep arn | tr -d \",' ' | 
            while read -r CERTIFICATE_ARN
            do
                # Detach the principal from the Thing resource.
                aws iot detach-thing-principal \
                    --region $AWS_PROVISIONING_REGION \
                    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT \
                    --principal $CERTIFICATE_ARN

                CERTIFICATE_ID=$(echo $CERTIFICATE_ARN | cut -d '/' -f2)

                aws iot update-certificate \
                    --region $AWS_PROVISIONING_REGION \
                    --certificate-id $CERTIFICATE_ID \
                    --new-status INACTIVE

                aws iot delete-certificate \
                    --region $AWS_PROVISIONING_REGION \
                    --certificate-id $CERTIFICATE_ID \
                    --force-delete
            done
aws iot delete-thing \
    --region $AWS_PROVISIONING_REGION \
    --thing-name "ThingPrefix_"$SERIAL_NUMBER_DEVICE_CONTEXT

# Make best effort to delete any inactive certificate that may have been created by the integration tests.
aws iot list-certificates \
    --region $AWS_PROVISIONING_REGION | \
        jq -c '.certificates[] | select(.status | contains("INACTIVE")) | .certificateArn' | \
            tr -d \" | \
                while read -r cert_arn 
                do 
                    CERTIFICATE_ID=$(echo $cert_arn | cut -d '/' -f2)
                    # Attempt to delete the certificate (and ignore any errors that come with 
                    # the deletion request).
                    aws iot delete-certificate \
                        --region $AWS_PROVISIONING_REGION \
                        --certificate-id $CERTIFICATE_ID \
                        --force-delete | \
                            echo true
                done

teardown