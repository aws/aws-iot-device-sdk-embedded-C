#!/bin/sh

# Travis CI uses this script to check GitHub commits. It builds the
# demos and tests, then runs the demos and tests against AWS IoT with
# the appropriate credentials.

# Exit on any nonzero return code.
set -e

# Set Thing Name.
AWS_IOT_THING_NAME="$AWS_IOT_THING_NAME_PREFIX$CC"

# Additional options for compilation.
COMPILER_OPTIONS="-Wall -Wextra -fsanitize=thread"

# Create build directory.
mkdir -p build
cd build
rm -rf *

# Create directory for credentials.
mkdir ../credentials

# Download Amazon Root CA 1.
wget https://www.amazontrust.com/repository/AmazonRootCA1.pem -O ../credentials/AmazonRootCA1.pem

# Write the client certificate and private key into files.
echo -e $AWS_IOT_CLIENT_CERT > ../credentials/clientCert.pem
echo -e $AWS_IOT_PRIVATE_KEY > ../credentials/privateKey.pem

# Build tests and demos against AWS IoT with ThreadSanitizer.
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DIOT_TEST_SERVER=\"\\\"$AWS_IOT_ENDPOINT\\\"\" -DIOT_TEST_PORT=443 -DIOT_TEST_ROOT_CA=\"\\\"../credentials/AmazonRootCA1.pem\\\"\" -DIOT_TEST_CLIENT_CERT=\"\\\"../credentials/clientCert.pem\\\"\" -DIOT_TEST_PRIVATE_KEY=\"\\\"../credentials/privateKey.pem\\\"\" -DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_LOG_LEVEL_DEMO=IOT_LOG_INFO -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" $COMPILER_OPTIONS"
make

# Run common tests (no network required).
./bin/iot_tests_common

# Run MQTT tests and demo against AWS IoT.
./bin/iot_tests_mqtt
./bin/iot_demo_mqtt -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME"

# Run Shadow tests and demo.
./bin/aws_iot_tests_shadow
./bin/aws_iot_demo_shadow -h "$AWS_IOT_ENDPOINT" -p 443 -s -r ../credentials/AmazonRootCA1.pem -c ../credentials/clientCert.pem -k ../credentials/privateKey.pem -i "$AWS_IOT_THING_NAME"

# Rebuild in static memory mode.
rm -rf *
cmake .. -DIOT_BUILD_TESTS=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_C_FLAGS="-DIOT_TEST_SERVER=\"\\\"$AWS_IOT_ENDPOINT\\\"\" -DIOT_TEST_PORT=443 -DIOT_TEST_ROOT_CA=\"\\\"../credentials/AmazonRootCA1.pem\\\"\" -DIOT_TEST_CLIENT_CERT=\"\\\"../credentials/clientCert.pem\\\"\" -DIOT_TEST_PRIVATE_KEY=\"\\\"../credentials/privateKey.pem\\\"\" -DIOT_STATIC_MEMORY_ONLY=1 -DIOT_TEST_MQTT_CLIENT_IDENTIFIER=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DAWS_IOT_TEST_SHADOW_THING_NAME=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_TEST_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" -DIOT_LOG_LEVEL_DEMO=IOT_LOG_INFO -DIOT_DEMO_MQTT_TOPIC_PREFIX=\"\\\"$AWS_IOT_THING_NAME\\\"\" $COMPILER_OPTIONS"
make

# Run common tests in static memory mode (no network required).
./bin/iot_tests_common

# Run MQTT and Shadow tests in static memory mode.
./bin/iot_tests_mqtt
./bin/aws_iot_tests_shadow
