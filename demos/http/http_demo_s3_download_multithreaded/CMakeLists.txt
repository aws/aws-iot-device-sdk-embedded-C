set( DEMO_NAME "http_demo_s3_download_multithreaded" )

# Include HTTP library's source and header path variables.
include( ${ROOT_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${ROOT_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the coreHTTP library
file( GLOB DEMO_FILE "${DEMO_NAME}.c*" )

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
        ${DEMOS_DIR}/http/common/src/http_demo_url_utils.c
        ${DEMOS_DIR}/http/common/src/http_demo_utils.c
        ${HTTP_SOURCES}
        ${HTTP_THIRD_PARTY_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        clock_posix
        openssl_posix
        ${LIB_RT}
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${DEMOS_DIR}/http/common/include"
        ${HTTP_INCLUDE_PUBLIC_DIRS}
        ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
        ${HTTP_INCLUDE_THIRD_PARTY_DIRS}
        ${HTTP_INCLUDE_PRIVATE_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "S3_PRESIGNED_GET_URL"
                        "HTTPS_PORT"
                        "ROOT_CA_CERT_PATH")
