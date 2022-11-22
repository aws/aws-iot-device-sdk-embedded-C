set( DEMO_NAME "greengrass_demo_local_auth" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the coreMQTT library
file( GLOB DEMO_FILE "${DEMO_NAME}.c*" )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_FILE}"
        "openssl_posix.c"
        ${MQTT_SOURCES}
        ${MQTT_SERIALIZER_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

find_package(OpenSSL)

target_link_libraries(
    ${DEMO_NAME}
    PUBLIC
        clock_posix
        sockets_posix
        ${OPENSSL_LIBRARIES}
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
                        "GREENGRASS_ADDRESS"
                        "ROOT_CA_CERT_PATH"
                        "THING_NAME"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH")
