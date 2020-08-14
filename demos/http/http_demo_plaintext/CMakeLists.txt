set( DEMO_NAME "http_demo_plaintext" )
# Demo target.
add_executable(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        http
        plaintext_posix   
)

target_include_directories(
    http
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
)

if(SERVER_HOST)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            SERVER_HOST="${SERVER_HOST}"
    )
endif()
