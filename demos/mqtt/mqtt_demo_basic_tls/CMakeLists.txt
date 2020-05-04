# Demo target.
set( CURRENT_MODULE "mqtt_demo_basic_tls" )
add_executable(${CURRENT_MODULE})

target_sources(
    ${CURRENT_MODULE}
    PUBLIC
        "${CMAKE_CURRENT_LIST_DIR}/${CURRENT_MODULE}.c"
)

target_link_libraries(
    ${CURRENT_MODULE}
    PRIVATE
        iotmqtt   
)

add_dependencies()

target_include_directories(
    iotmqtt
    PUBLIC
    ${CMAKE_CURRENT_LIST_DIR}
)
