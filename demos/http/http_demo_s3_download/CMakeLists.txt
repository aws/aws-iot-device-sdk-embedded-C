set( DEMO_NAME "http_demo_s3_download" )

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Include coreJSON library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )

# Include sigV4 library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/aws/sigv4-for-aws-iot-embedded-sdk/sigv4FilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the coreHTTP library
file( GLOB DEMO_FILE "${DEMO_NAME}.c*" )
file( GLOB DEMO_UTILS "${DEMOS_DIR}/http/common/src/*.c*" )

# Disable some warnings for llhttp sources.
set_source_files_properties(
    ${HTTP_SOURCES}
    PROPERTIES
    COMPILE_FLAGS "-Wno-unused-parameter"
)

# Demo target.
add_executable(
    ${DEMO_NAME}
    "${DEMO_FILE}"
    ${DEMO_UTILS}
    ${HTTP_SOURCES}
    ${HTTP_THIRD_PARTY_SOURCES}
    ${BACKOFF_ALGORITHM_SOURCES}
    ${JSON_SOURCES}
    ${SIGV4_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        clock_posix
        openssl_posix
        mbedtls
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${DEMOS_DIR}/http/common/include"
        ${HTTP_INCLUDE_PUBLIC_DIRS}
        ${JSON_INCLUDE_PUBLIC_DIRS}
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${HTTP_INCLUDE_THIRD_PARTY_DIRS}
        ${HTTP_INCLUDE_PRIVATE_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
        ${SIGV4_INCLUDE_PUBLIC_DIRS}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "HTTPS_PORT"
                        "ROOT_CA_CERT_PATH"
                        "ROOT_CA_CERT_PATH_S3"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "AWS_IOT_THING_NAME"
                        "AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT"
                        "AWS_IOT_CREDENTIAL_PROVIDER_ROLE"
                        "AWS_S3_BUCKET_NAME"
                        "AWS_S3_BUCKET_REGION"
                        "AWS_S3_OBJECT_NAME")
