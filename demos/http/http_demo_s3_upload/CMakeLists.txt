set( DEMO_NAME "http_demo_s3_upload" )

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_NAME}.c"
        "${DEMOS_DIR}/http/common/src/http_demo_utils.c"
        ${HTTP_SOURCES}
        ${HTTP_THIRD_PARTY_SOURCES}
        ${BACKOFF_ALGORITHM_SOURCES}
)

# Add to default target if all required macros needed to run this demo are defined
check_presigned_urls(${DEMO_NAME})

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        clock_posix
        openssl_posix
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

if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()

if(HTTPS_PORT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            HTTPS_PORT=${HTTPS_PORT}
    )
endif()
