set( LIBRARY_NAME "mqtt_subscription_manager" )
# Library target.
add_library(${LIBRARY_NAME}
            "${LIBRARY_NAME}.c" )

target_link_libraries(
    ${LIBRARY_NAME}
    PRIVATE
        mqtt
)

target_include_directories(
    ${LIBRARY_NAME}
    PUBLIC
        ${LOGGING_INCLUDE_DIRS}
)

