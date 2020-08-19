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

if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(BROKER_ENDPOINT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            BROKER_ENDPOINT="${BROKER_ENDPOINT}"
    )
endif()
if(CLIENT_IDENTIFIER)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            CLIENT_IDENTIFIER="${CLIENT_IDENTIFIER}"
    )
endif()
