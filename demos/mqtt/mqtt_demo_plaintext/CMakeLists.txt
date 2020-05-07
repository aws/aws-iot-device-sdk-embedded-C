# Include filePaths for variables below.
include(filePaths.cmake)

# Demo target.
add_executable(${DEMO_NAME})

target_sources(
    ${DEMO_NAME}
    PRIVATE
        ${MQTT_DEMO_PLAINTEXT_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        ${MQTT_DEMO_PLAINTEXT_LIBRARIES}   
)

target_include_directories(
    mqtt
    PUBLIC
        ${MQTT_DEMO_PLAINTEXT_INCLUDE_PUBLIC_DIRS}
)
