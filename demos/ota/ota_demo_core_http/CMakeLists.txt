set( DEMO_NAME "ota_demo_core_http" )

# Include required library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/ota-for-aws-iot-embedded-sdk/otaFilePaths.cmake )
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Disable some warnings for llhttp sources.
set_source_files_properties(
    ${HTTP_SOURCES}
    PROPERTIES
    COMPILE_FLAGS "-Wno-unused-parameter"
)

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_NAME}.c"
        "${DEMOS_DIR}/ota/common/src/mqtt_subscription_manager.c"
        "${DEMOS_DIR}/http/common/src/http_demo_url_utils.c"
        ${OTA_SOURCES}
        ${OTA_OS_POSIX_SOURCES}
        ${OTA_MQTT_SOURCES}
        ${OTA_HTTP_SOURCES}
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
        ${HTTP_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        ${LIB_RT}
        ota_pal
        Threads::Threads
        clock_posix
        openssl_posix
        aws_iot_json
        tinycbor
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${DEMOS_DIR}/ota/common/include"
        "${DEMOS_DIR}/http/common/include"
        "${CMAKE_CURRENT_LIST_DIR}"
        "${LOGGING_INCLUDE_DIRS}"
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${OTA_INCLUDE_PUBLIC_DIRS}
        ${OTA_INCLUDE_PRIVATE_DIRS}
        ${OTA_INCLUDE_OS_POSIX_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${HTTP_INCLUDE_PUBLIC_DIRS}
        ${AWS_DEMO_INCLUDE_DIRS}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "ROOT_CA_CERT_PATH_HTTP"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "CLIENT_IDENTIFIER"
                      OPTIONAL
                        "CLIENT_USERNAME"
                        "CLIENT_PASSWORD"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME")
