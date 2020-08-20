set( DEMO_NAME "mqtt_demo_lightweight" )
# Demo target.
add_executable(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
)

# Treat warnings as error for demo target.
target_compile_options( ${DEMO_NAME} PUBLIC "-Werror" )  

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mqtt
        clock_posix
        plaintext_posix
        transport_reconnect_posix   
)

target_include_directories(
    mqtt
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
)

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
