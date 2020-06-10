set( DEMO_NAME "mqtt_demo_basic_tls" )
# Demo target.
add_executable(${DEMO_NAME})

set(OPENSSL_USE_STATIC_LIBS TRUE)
find_package(OpenSSL REQUIRED)

set( CMAKE_THREAD_PREFER_PTHREAD ON )
find_package(Threads REQUIRED)

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "${DEMO_NAME}.c"
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mqtt
        OpenSSL::Crypto
        OpenSSL::SSL
	# SSL uses Threads and on some platforms require explicit linking.
        Threads::Threads
	# SSL uses Dynamic Loading and on some platforms requires explicit linking.
        ${CMAKE_DL_LIBS}
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

#Copy the server certificate file to the binary directory.
add_custom_command(
    TARGET
        ${DEMO_NAME}
    POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
        "${CMAKE_CURRENT_LIST_DIR}/mosquitto.org.crt"
        "$<TARGET_FILE_DIR:${DEMO_NAME}>/certificates/mosquitto.org.crt"
)
