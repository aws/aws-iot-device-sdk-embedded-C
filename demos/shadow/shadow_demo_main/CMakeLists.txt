include(CheckSymbolExists)

set( DEMO_NAME "shadow_demo_main" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include Shadow library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/shadowFilePaths.cmake )

# Include JSON library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )

# Demo target.
add_executable(${DEMO_NAME})

# Add to default target if all required macros needed to run this demo are defined
check_aws_credentials(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
        "shadow_demo_helpers.c"
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
        ${SHADOW_SOURCES}
        ${JSON_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        clock_posix
        openssl_posix
        retry_utils_posix
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${MQTT_INCLUDE_PRIVATE_DIRS}
        ${SHADOW_INCLUDE_PUBLIC_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${JSON_INCLUDE_PUBLIC_DIRS}
)

if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(CLIENT_IDENTIFIER)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            CLIENT_IDENTIFIER="${CLIENT_IDENTIFIER}"
    )
endif()
