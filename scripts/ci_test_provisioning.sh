#!/bin/sh

# Travis CI uses this script to test the Provisioning library.

# Exit on any nonzero return code.
set -exu

# First we will make sure that a JSON parser utility is available.
jq --version || { echo "Need to have the jq utility installed for AWS CLI command output parsing" && false; }

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

    # Create a provisioning role, if it does not exist in the account. If a new one is created, we add some delay time (10 sec) for the role to be available
    # (IAM role creation is "eventually consistent"). If the provisioning role already exists, then ignore errors. 
    # SUGGESTION: Do not delete the Provisioning Role from the account to ensure that the setup executes reliably.
    aws iam create-role \
        --role-name $PROVISIONING_ROLE_NAME \
        --assume-role-policy-document '{"Version":"2012-10-17","Statement":[{"Action":"sts:AssumeRole","Effect":"Allow","Principal":{"Service":"iot.amazonaws.com"}}]}' && sleep 10 \
            || true
    aws iam attach-role-policy \
        --region $AWS_PROVISIONING_REGION \
        --role-name $PROVISIONING_ROLE_NAME \
        --policy-arn arn:aws:iam::aws:policy/service-role/AWSIoTThingsRegistration  || true

    # Delete an existing fleet provisioning template by the same name, if it exists. Ignore the error if the template does not exist.
    aws iot delete-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME || true

    # Add a single provisioning template to test with.
    aws iot create-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME \
        --provisioning-role-arn arn:aws:iam::$AWS_ACCOUNT_ID:role/$PROVISIONING_ROLE_NAME \
        --template-body  "{\"Parameters\":{\"DeviceLocation\":{\"Type\":\"String\"},\"AWS::IoT::Certificate::Id\":{\"Type\":\"String\"},\"SerialNumber\":{\"Type\":\"String\"}},\"Mappings\":{\"LocationTable\":{\"Seattle\":{\"LocationUrl\":\"https://example.aws\"}}},\"Resources\":{\"thing\":{\"Type\":\"AWS::IoT::Thing\",\"Properties\":{\"ThingName\":{\"Fn::Join\":[\"\",[\"ThingPrefix_\",{\"Ref\":\"SerialNumber\"}]]},\"AttributePayload\":{\"version\":\"v1\",\"serialNumber\":\"serialNumber\"}},\"OverrideSettings\":{\"AttributePayload\":\"MERGE\",\"ThingTypeName\":\"REPLACE\",\"ThingGroups\":\"DO_NOTHING\"}},\"certificate\":{\"Type\":\"AWS::IoT::Certificate\",\"Properties\":{\"CertificateId\":{\"Ref\":\"AWS::IoT::Certificate::Id\"},\"Status\":\"Active\"},\"OverrideSettings\":{\"Status\":\"REPLACE\"}},\"policy\":{\"Type\":\"AWS::IoT::Policy\",\"Properties\":{\"PolicyDocument\":{\"Version\":\"2012-10-17\",\"Statement\":[{\"Effect\":\"Allow\",\"Action\":[\"iot:Connect\",\"iot:Subscribe\",\"iot:Publish\",\"iot:Receive\"],\"Resource\":\"*\"}]}}}},\"DeviceConfiguration\":{\"FallbackUrl\":\"https://www.example.com/test-site\",\"LocationUrl\":{\"Fn::FindInMap\":[\"LocationTable\",{\"Ref\":\"DeviceLocation\"},\"LocationUrl\"]}}}" \
        --enabled 
}

# Cleanup the created resources created by the integration tests on the AWS IoT account.
# (Resources include Thing, its attached certificates and their policies, Fleet Provisioning Template)
# Note - We do not delete the Provisioning Role as the immediate availability of an IAM role that is created on every CI script run is not guaranteed
# (due to the eventually consistent characterstic of the IAM role creation).
teardown() {
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
                            --force-delete || true
                    done
                    
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

    # Delete Fleet Provisioning Template.
    aws iot delete-provisioning-template \
        --region $AWS_PROVISIONING_REGION \
        --template-name $TEMPLATE_NAME
}

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    # Setup the AWS IoT account for integration tests.
    setup

    # Parameters to inject in the integration test to pass as provisioning parameters.
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

    # Compiler flags for integration tests.
    COMMON_CMAKE_C_FLAGS="$AWS_IOT_CREDENTIAL_DEFINES -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS=\"$PROVISIONING_PARAMETERS\""

    # Run teardown routine if we ever encounter a failure for best effort to cleanup resources on the AWS IoT account.
    # We register on the EXIT signal as the set -e flag will convert errors to EXIT.
    trap "teardown" EXIT
else
    # No compiler flags needed for unit tests.
    COMMON_CMAKE_C_FLAGS=""
fi        

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

if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    teardown

    # Reset the signal handler for EXIT signal.
    trap - EXIT
fi