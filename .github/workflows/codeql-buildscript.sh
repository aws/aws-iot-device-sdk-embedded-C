#!/usr/bin/env bash

#https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/929a86dbbd9bb546872b383e955f8b420448c3e9/.github/workflows/ci.yml#L20

sudo apt-get update -y
sudo apt-get install -y libssl-dev libmosquitto-dev
curl https://cmake.org/files/v3.2/cmake-3.2.0-Linux-x86_64.tar.gz -o cmake.tar.gz
tar -xf cmake.tar.gz
mkdir build && cd build
../cmake-3.2.0-Linux-x86_64/bin/cmake .. \
-G "Unix Makefiles" \
-DBUILD_DEMOS=1 \
-DCMAKE_BUILD_TYPE=Release \
-DCMAKE_C_FLAGS='-Wall -Wextra -Werror' \
-DAWS_IOT_ENDPOINT="aws-iot-endpoint" \
-DBROKER_ENDPOINT="broker-endpoint" \
-DCLIENT_CERT_PATH="cert/path" \
-DROOT_CA_CERT_PATH="cert/path" \
-DCLIENT_PRIVATE_KEY_PATH="key/path" \
-DCLIENT_IDENTIFIER="ci-identifier" \
-DTHING_NAME="thing-name" \
-DS3_PRESIGNED_GET_URL="get-url" \
-DS3_PRESIGNED_PUT_URL="put-url" \
-DCLAIM_CERT_PATH="cert/path" \
-DCLAIM_PRIVATE_KEY_PATH="key/path" \
-DPROVISIONING_TEMPLATE_NAME="template-name" \
-DDEVICE_SERIAL_NUMBER="00000" \
-DCSR_SUBJECT_NAME="CN=Fleet Provisioning Demo" \
-DGREENGRASS_ADDRESS="greengrass-address"

cd ..
make -C build/ help | grep demo | tr -d '. ' | xargs make -C build/
make -C demos/jobs/jobs_demo_mosquitto
