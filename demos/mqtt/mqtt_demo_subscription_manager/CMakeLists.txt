include(CheckSymbolExists)

# Include CMake configuration for subscriptipn manager library.
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/subscription-manager )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

set( DEMO_NAME "mqtt_demo_subscription_manager" )

# Demo target.
add_executable(${DEMO_NAME})

# Add to default target if all required macros needed to run this demo are defined
check_aws_credentials(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mqtt_subscription_manager
        clock_posix
        openssl_posix
        retry_utils_posix
)

target_include_directories(
    mqtt_subscription_manager
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}/subscription-manager
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${MQTT_INCLUDE_PRIVATE_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

# Set preprocess defines for demo, if passed through CMake build.
if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(BROKER_ENDPOINT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            BROKER_ENDPOINT="${BROKER_ENDPOINT}"
    )
endif()
if(CLIENT_IDENTIFIER)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            CLIENT_IDENTIFIER="${CLIENT_IDENTIFIER}"
    )
endif()