# Include CMake configuration for subscriptipn manager library.
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/subscription-manager )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

set( DEMO_NAME "mqtt_demo_subscription_manager" )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the coreMQTT library
file( GLOB DEMO_FILE "${DEMO_NAME}.c*" )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_FILE}"
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mqtt_subscription_manager
        clock_posix
        openssl_posix
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
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "ROOT_CA_CERT_PATH"
                        "BROKER_ENDPOINT"
                        "BROKER_PORT"
                        "CLIENT_IDENTIFIER")
