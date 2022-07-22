set( DEMO_NAME "defender_demo" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include JSON library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )

# Include Defender library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/device-defender-for-aws-iot-embedded-sdk/defenderFilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the Device Defender library
file( GLOB DEMO_SRCS "*.c*" )

# Demo target.
add_executable( ${DEMO_NAME}
                ${DEMO_SRCS}
                ${MQTT_SOURCES}
                ${MQTT_SERIALIZER_SOURCES}
                ${BACKOFF_ALGORITHM_SOURCES}
                ${JSON_SOURCES}
                ${DEFENDER_SOURCES} )

target_link_libraries( ${DEMO_NAME} PRIVATE
                       clock_posix
                       openssl_posix )

target_include_directories( ${DEMO_NAME} PUBLIC
                            ${LOGGING_INCLUDE_DIRS}
                            ${MQTT_INCLUDE_PUBLIC_DIRS}
                            ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
                            ${JSON_INCLUDE_PUBLIC_DIRS}
                            ${DEFENDER_INCLUDE_PUBLIC_DIRS}
                            ${AWS_DEMO_INCLUDE_DIRS}
                            ${CMAKE_CURRENT_LIST_DIR} )

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "THING_NAME"
                        "CLIENT_IDENTIFIER"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME")
