include( CheckSymbolExists )

set( DEMO_NAME "defender_demo" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include JSON library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )

# Include Defender library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/device-defender-for-aws-iot-embedded-sdk/defenderFilePaths.cmake )

# Demo target.
add_executable( ${DEMO_NAME}
                "defender_demo.c"
                "metrics_collector.c"
                "mqtt_operations.c"
                "report_builder.c"
                ${MQTT_SOURCES}
                ${MQTT_SERIALIZER_SOURCES}
                ${JSON_SOURCES}
                ${DEFENDER_SOURCES} )

# Add to default target if all required macros needed to run this demo are defined.
check_aws_credentials( ${DEMO_NAME} )

target_link_libraries( ${DEMO_NAME} PRIVATE
                       clock_posix
                       openssl_posix )

target_include_directories( ${DEMO_NAME} PUBLIC
                            ${LOGGING_INCLUDE_DIRS}
                            ${MQTT_INCLUDE_PUBLIC_DIRS}
                            ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
                            ${JSON_INCLUDE_PUBLIC_DIRS}
                            ${DEFENDER_INCLUDE_PUBLIC_DIRS}
                            ${CMAKE_CURRENT_LIST_DIR} )

if( ROOT_CA_CERT_PATH )
    target_compile_definitions( ${DEMO_NAME} PRIVATE
                                ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}" )
endif()

if( CLIENT_IDENTIFIER )
    target_compile_definitions( ${DEMO_NAME} PRIVATE
                                CLIENT_IDENTIFIER="${CLIENT_IDENTIFIER}" )
endif()

if( THING_NAME )
    target_compile_definitions( ${DEMO_NAME} PRIVATE
                                THING_NAME="${THING_NAME}" )
endif()
