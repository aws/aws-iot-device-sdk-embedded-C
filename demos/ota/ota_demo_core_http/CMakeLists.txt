set( DEMO_NAME "ota_demo_core_http" )

# Include required library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/ota/otaFilePaths.cmake )
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )
# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Demo target.
add_executable(${DEMO_NAME})

# librt is required to use OTA OS POSIX port.
find_library(LIB_RT rt REQUIRED)

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "ota_demo_core_http.c"
        "ota_pal_posix.c"
        "${DEMOS_DIR}/ota/common/src/mqtt_subscription_manager.c"
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
        pthread
        clock_posix
        openssl_posix
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${DEMOS_DIR}/ota/common/include"
        "${CMAKE_CURRENT_LIST_DIR}"
        "${LOGGING_INCLUDE_DIRS}"
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${OTA_INCLUDE_PUBLIC_DIRS}
        ${OTA_INCLUDE_PRIVATE_DIRS}
        ${OTA_INCLUDE_OS_POSIX_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${HTTP_INCLUDE_PUBLIC_DIRS}
)

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
