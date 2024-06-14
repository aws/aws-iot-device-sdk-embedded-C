set( DEMO_NAME "fleet_provisioning_with_csr_demo" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include Fleet Provisioning library's source and header path variables.
include(
    ${CMAKE_SOURCE_DIR}/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/fleetprovisioningFilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the Fleet Provisioning library
file( GLOB DEMO_SRCS "*.c*" )

# Demo target.
add_executable( ${DEMO_NAME}
                ${DEMO_SRCS}
                ${MQTT_SOURCES}
                ${MQTT_SERIALIZER_SOURCES}
                ${BACKOFF_ALGORITHM_SOURCES}
                ${FLEET_PROVISIONING_SOURCES} )

target_link_libraries( ${DEMO_NAME} PRIVATE
                       tinycbor
                       mbedtls
                       clock_posix
                       transport_mbedtls_posix )

target_include_directories( ${DEMO_NAME}
                            PUBLIC
                              ${LOGGING_INCLUDE_DIRS}
                              ${MQTT_INCLUDE_PUBLIC_DIRS}
                              ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
                              ${AWS_DEMO_INCLUDE_DIRS}
                              ${FLEET_PROVISIONING_INCLUDE_PUBLIC_DIRS}
                              ${CMAKE_SOURCE_DIR}/platform/include
                              ${CMAKE_CURRENT_LIST_DIR} )

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLAIM_CERT_PATH"
                        "CLAIM_PRIVATE_KEY_PATH"
                        "PROVISIONING_TEMPLATE_NAME"
                        "DEVICE_SERIAL_NUMBER"
                        "CSR_SUBJECT_NAME"
                        "CLIENT_IDENTIFIER"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "CLIENT_CERT_PATH")
