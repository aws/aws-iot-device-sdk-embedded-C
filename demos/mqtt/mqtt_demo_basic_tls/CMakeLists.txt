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
        Threads::Threads
        ${CMAKE_DL_LIBS}
)

target_include_directories(
    mqtt
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)
