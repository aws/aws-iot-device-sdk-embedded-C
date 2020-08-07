include(CheckSymbolExists)

set( DEMO_NAME "shadow_demo_main" )

# Demo target.
add_executable(${DEMO_NAME})

# Add to default target if all required macros needed to run this demo are defined
check_aws_credentials(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
        "shadow_demo_helpers.c"
)

# JSON library Public Include directories.
set( JSON_INCLUDE_PUBLIC_DIRS
     "${MODULES_DIR}/standard/json/include" )

# JSON library source files.
set( JSON_SOURCES
     "${MODULES_DIR}/standard/json/src/json.c" )

# Create target for JSON utility.
add_library( json
                ${JSON_SOURCES} )

# JSON library Public Include directories.
target_include_directories( json
                            PUBLIC
                                "${MODULES_DIR}/standard/json/include" )

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mqtt
        shadow
        json
        clock_posix
        openssl_posix
        transport_reconnect_posix
)

target_include_directories(
    shadow
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
)

# Download the Amazon Root CA certificate.
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
