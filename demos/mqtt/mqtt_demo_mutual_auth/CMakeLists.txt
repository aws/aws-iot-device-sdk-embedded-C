set( DEMO_NAME "mqtt_demo_mutual_auth" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_NAME}.c"
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        clock_posix
        openssl_posix
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "CLIENT_IDENTIFIER"
                      OPTIONAL
                        "CLIENT_USERNAME"
                        "CLIENT_PASSWORD"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME")
