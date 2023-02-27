set( DEMO_NAME "shadow_demo_main" )

# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include Shadow library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/shadowFilePaths.cmake )

# Set path to corePKCS11 and it's third party libraries.
set(COREPKCS11_LOCATION "${CMAKE_SOURCE_DIR}/libraries/standard/corePKCS11")
set(CORE_PKCS11_3RDPARTY_LOCATION "${COREPKCS11_LOCATION}/source/dependency/3rdparty")

# Include PKCS #11 library's source and header path variables.
include( ${COREPKCS11_LOCATION}/pkcsFilePaths.cmake )

list(APPEND PKCS_SOURCES
    "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils/mbedtls_utils.c"
)

# Include JSON library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the Device Shadow library
file( GLOB DEMO_SRCS "shadow_demo_helpers.c" "*.c*" )

# Demo target.
add_executable(
    ${DEMO_NAME}
    ${DEMO_SRCS}
    ${MQTT_SOURCES}
    ${MQTT_SERIALIZER_SOURCES}
    ${BACKOFF_ALGORITHM_SOURCES}
    ${PKCS_SOURCES}
    ${PKCS_PAL_POSIX_SOURCES}
    ${SHADOW_SOURCES}
    ${JSON_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
    mbedtls
    transport_mbedtls_pkcs11_posix
    clock_posix
    openssl_posix
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${PKCS_INCLUDE_PUBLIC_DIRS}
        ${PKCS_PAL_INCLUDE_PUBLIC_DIRS}	
        ${SHADOW_INCLUDE_PUBLIC_DIRS}
        ${JSON_INCLUDE_PUBLIC_DIRS}
        ${AWS_DEMO_INCLUDE_DIRS}
        "${DEMOS_DIR}/pkcs11/common/include" # corePKCS11 config
        "${CMAKE_SOURCE_DIR}/platform/include"
        "${CMAKE_CURRENT_LIST_DIR}"
        PRIVATE
        "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils" )

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "CLIENT_IDENTIFIER"
                        "THING_NAME"
                        "SSL_USED_OPENSSL"
                        "SSL_USED_MBEDTLS"
                        "OS_NAME"
                        "OS_VERSION"
                        "HARDWARE_PLATFORM_NAME")
