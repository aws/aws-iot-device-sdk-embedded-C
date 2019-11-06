#!/bin/sh

# Travis CI uses this script to test the Onboarding library.

# Exit on any nonzero return code.
set -exu

TRAVIS_PULL_REQUEST=false

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
        --endpoint https://beta.us-east-1.iot.amazonaws.com \
        --template-name $TEMPLATE_NAME | echo true
    
    # Add a single provisioning template to test with.
    aws iot create-provisioning-template \
        --endpoint https://beta.us-east-1.iot.amazonaws.com \
        --template-name CI_TEST_NAME \
        --provisioning-role-arn arn:aws:iam::502387646363:role/Admin \
        --template-body "{  \"Parameters\" : {     \"DeviceLocation\": {       \"Type\": \"String\"     }  },  \"Mappings\": {    \"LocationTable\": {      \"Seattle\": {        \"LocationUrl\": \"https:\/\/example.aws\"      }    }  },  \"Resources\" : {    \"thing\" : {      \"Type\" : \"AWS::IoT::Thing\",      \"Properties\" : {        \"ThingName\" : \"ThingName\",        \"AttributePayload\" : { \"version\" : \"v1\", \"serialNumber\" : \"serialNumber\"},        \"ThingTypeName\" :  \"lightBulb-versionA\",        \"ThingGroups\" : [\"v1-lightbulbs\", \"WA\"],        \"BillingGroup\": \"BillingGroup\"      },      \"OverrideSettings\" : {        \"AttributePayload\" : \"MERGE\",        \"ThingTypeName\" : \"REPLACE\",        \"ThingGroups\" : \"DO_NOTHING\"      }    },    \"certificate\" : {      \"Type\" : \"AWS::IoT::Certificate\",      \"Properties\" : {        \"Status\" : \"Active\"      },      \"OverrideSettings\" : {        \"Status\" : \"DO_NOTHING\"      }    },    \"policy\" : {      \"Type\" : \"AWS::IoT::Policy\",      \"Properties\" : {        \"PolicyDocument\" : {          \"Version\": \"2012-10-17\",          \"Statement\": [{            \"Effect\": \"Allow\",            \"Action\":[\"iot:Publish\"],            \"Resource\": [\"arn:aws:iot:us-east-1:123456789012:topic\/foo\/bar\"]          }]        }      }    }  },  \"DeviceConfiguration\": {    \"FallbackUrl\": \"https:\/\/www.example.com\/test-site\",    \"LocationUrl\": {\"Fn::FindInMap\": [\"LocationTable\", {\"Ref\": \"DeviceLocation\"}, \"LocationUrl\"]}  }}" \
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

COMMON_CMAKE_FLAGS="-DAWS_IOT_TEST_ONBOARDING_TEMPLATE_NAME=\"\\\"$TEMPLATE_NAME\\\"\" -DAWS_IOT_TEST_ONBOARDING_TEMPLATE_PARAMETERS=\"$PROVISION_PARAMETERS\""

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
