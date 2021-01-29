set( DEMO_NAME "http_demo_mutual_auth" )

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
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(AWS_HTTPS_PORT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            AWS_HTTPS_PORT=${AWS_HTTPS_PORT}
    )
endif()
set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "SERVER_HOST"
                        "AWS_HTTPS_PORT"
                        "ROOT_CA_CERT_PATH")
set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "ROOT_CA_CERT_PATH")
