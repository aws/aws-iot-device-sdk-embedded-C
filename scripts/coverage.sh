#!/bin/sh

# Travis CI uses this script to build an submit code coverage results.

# Exit on any nonzero return code.
set -e

# Set Thing Name.
AWS_IOT_THING_NAME="$AWS_IOT_THING_NAME_PREFIX$CC"

# Delete everything in the build directory.
mkdir -p build
cd build
rm -rf *

# Build tests and demos against AWS IoT with gcov.
cmake .. -DAWS_IOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DAWS_IOT_TEST_SERVER=\"\\\"$AWS_IOT_ENDPOINT\\\"\" -DAWS_IOT_TEST_PORT=443 -DAWS_IOT_TEST_ROOT_CA=\"\\\"../credentials/AmazonRootCA1.pem\\\"\" -DAWS_IOT_TEST_CLIENT_CERT=\"\\\"../credentials/clientCert.pem\\\"\" -DAWS_IOT_TEST_PRIVATE_KEY=\"\\\"../credentials/privateKey.pem\\\"\" -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_LOG_LEVEL_DEMO=AWS_IOT_LOG_INFO --coverage"
make

# Run MQTT tests and demo against AWS IoT with code coverage.
./bin/aws_iot_tests_mqtt
./bin/aws_iot_demo_mqtt -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME"

# Run Shadow tests and demo with code coverage.
./bin/aws_iot_tests_shadow
./bin/aws_iot_demo_shadow -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME"

# Generate code coverage results, excluding Unity test framework.
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '*unity*' --output-file coverage.info

# Submit the code coverage results.
cd ..
coveralls --lcov-file build/coverage.info
