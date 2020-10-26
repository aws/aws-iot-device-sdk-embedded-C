set( DEMO_NAME "http_demo_s3_download_multithreaded" )

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_NAME}.c"
        "../common/src/http_demo_utils.c"
        ${HTTP_SOURCES}
        ${HTTP_THIRD_PARTY_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        openssl_posix
        retry_utils_posix
        rt
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "../common/include"
        ${HTTP_INCLUDE_PUBLIC_DIRS}
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
if(S3_PRESIGNED_GET_URL)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            S3_PRESIGNED_GET_URL="${S3_PRESIGNED_GET_URL}"
    )
endif()
