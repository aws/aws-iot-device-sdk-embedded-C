include(filePaths.cmake)

add_executable(${DEMO_NAME})

set(OPENSSL_USE_STATIC_LIBS TRUE)
find_package(OpenSSL REQUIRED)

target_sources(
    ${DEMO_NAME}
    PRIVATE
        ${MQTT_DEMO_BASIC_TLS_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        ${MQTT_DEMO_BASIC_TLS_LIBRARIES}   
)

target_include_directories(
    mqtt
    PUBLIC
        ${MQTT_DEMO_BASIC_TLS_INCLUDE_PUBLIC_DIRS}
)
