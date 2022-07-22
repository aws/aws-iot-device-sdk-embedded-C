set( DEMO_NAME "http_demo_mutual_auth" )

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

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
        ${LOGGING_INCLUDE_DIRS}
        ${AWS_DEMO_INCLUDE_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
)

set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_HTTPS_PORT"
                        "ROOT_CA_CERT_PATH")
set_macro_definitions(TARGETS ${DEMO_NAME}
                      REQUIRED
                        "AWS_IOT_ENDPOINT"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "ROOT_CA_CERT_PATH")
