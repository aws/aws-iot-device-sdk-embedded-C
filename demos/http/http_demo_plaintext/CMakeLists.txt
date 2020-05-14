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
)

target_include_directories(
    http
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)
