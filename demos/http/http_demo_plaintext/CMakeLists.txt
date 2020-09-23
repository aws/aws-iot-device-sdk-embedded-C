set( DEMO_NAME "http_demo_plaintext" )

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Demo target.
add_executable(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
        "../common/src/http_demo_utils.c"
        ${HTTP_SOURCES}
        ${HTTP_THIRD_PARTY_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        plaintext_posix
        retry_utils_posix  
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

if(SERVER_HOST)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            SERVER_HOST="${SERVER_HOST}"
    )
endif()
if(HTTP_PORT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            HTTP_PORT=${HTTP_PORT}
    )
endif()
