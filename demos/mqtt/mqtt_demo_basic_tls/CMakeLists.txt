set( DEMO_NAME "mqtt_demo_basic_tls" )
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
        mqtt
        clock_posix
        openssl_posix
        transport_reconnect_posix
)

target_include_directories(
    mqtt
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
)

# Download the Mosquitto Root CA certificate.
message( "Downloading the Mosquitto Root CA certificate..." )
file(MAKE_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}/certificates)
execute_process(
    COMMAND curl --url https://test.mosquitto.org/ssl/mosquitto.org.crt
    -o ${CMAKE_CURRENT_LIST_DIR}/certificates/mosquitto.org.crt
)

# Copy the server certificate file to the binary directory.
add_custom_command(
    TARGET
        ${DEMO_NAME}
    POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
        "${CMAKE_CURRENT_LIST_DIR}/certificates/mosquitto.org.crt"
        "$<TARGET_FILE_DIR:${DEMO_NAME}>/certificates/mosquitto.org.crt"
)
