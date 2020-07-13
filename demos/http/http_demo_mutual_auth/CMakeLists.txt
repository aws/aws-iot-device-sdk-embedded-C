set( DEMO_NAME "http_demo_mutual_auth" )
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
        openssl_posix
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

# Download the Amazon Root CA certificate
message( "Downloading the Amazon Root CA certificate..." )
file(MAKE_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}/certificates)
execute_process(
    COMMAND curl --url https://www.amazontrust.com/repository/AmazonRootCA1.pem 
    -o ${CMAKE_CURRENT_LIST_DIR}/certificates/AmazonRootCA1.crt
)

# Copy the certificates and client key to the binary directory.
add_custom_command(
    TARGET
        ${DEMO_NAME}
    POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_directory
        "${CMAKE_CURRENT_LIST_DIR}/certificates"
        "$<TARGET_FILE_DIR:${DEMO_NAME}>/certificates"
)
