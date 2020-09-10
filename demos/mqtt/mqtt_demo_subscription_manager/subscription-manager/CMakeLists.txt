# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

set( LIBRARY_NAME "mqtt_subscription_manager" )
# Library target.
add_library( ${LIBRARY_NAME}
            "${LIBRARY_NAME}.c" )

target_include_directories(
    ${LIBRARY_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
)

