set( DEMO_NAME "ota_demo" )
# Demo target.
add_executable(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        "aws_iot_ota_update_demo.c"
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        # ota
        mqtt
        clock_posix
        openssl_posix
        transport_reconnect_posix
        mqtt_subscription_manager
)

target_include_directories(
    ota
    PUBLIC
        "${CMAKE_CURRENT_LIST_DIR}/.."
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${CMAKE_CURRENT_LIST_DIR}/.."
        "${LOGGING_INCLUDE_DIRS}"
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
