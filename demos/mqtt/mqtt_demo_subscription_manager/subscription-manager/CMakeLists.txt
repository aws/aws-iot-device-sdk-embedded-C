# Include MQTT library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

set( LIBRARY_NAME "mqtt_subscription_manager" )

# CPP files are searched for supporting CI build checks that verify C++ linkage of the coreMQTT library
file( GLOB LIBRARY_SRCS "${LIBRARY_NAME}.c*" )
# Library target.
add_library( ${LIBRARY_NAME}
             ${LIBRARY_SRCS} )

target_include_directories(
    ${LIBRARY_NAME}
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
        ${MQTT_INCLUDE_PUBLIC_DIRS}
)
