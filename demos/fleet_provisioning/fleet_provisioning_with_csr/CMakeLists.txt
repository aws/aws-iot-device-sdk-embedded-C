set( DEMO_NAME "fleet_provisioning_with_csr_demo" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include Fleet Provisioning library's source and header path variables.
include(
    ${CMAKE_SOURCE_DIR}/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/fleetprovisioningFilePaths.cmake )

# Demo target.
add_executable( ${DEMO_NAME}
                "fleet_provisioning_csr_demo.c"
                "mqtt_operations.c"
                ${MQTT_SOURCES}
                ${MQTT_SERIALIZER_SOURCES}
                ${BACKOFF_ALGORITHM_SOURCES}
                ${FLEET_PROVISIONING_SOURCES} )

target_link_libraries( ${DEMO_NAME} PRIVATE
                       tinycbor
                       clock_posix
                       openssl_posix )

target_include_directories( ${DEMO_NAME} PUBLIC
                            ${LOGGING_INCLUDE_DIRS}
                            ${MQTT_INCLUDE_PUBLIC_DIRS}
                            ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
                            ${FLEET_PROVISIONING_INCLUDE_PUBLIC_DIRS}
                            ${CMAKE_CURRENT_LIST_DIR} )

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLAIM_CERT_PATH"
                        "CLAIM_KEY_PATH"
                        "PROVISIONING_TEMPLATE_NAME"
                        "PROVISIONING_KEY_PATH"
                        "PROVISIONING_CSR_PATH"
                        "PROVISIONING_CERT_PATH"
                        "CLIENT_IDENTIFIER"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME")
