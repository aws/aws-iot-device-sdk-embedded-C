# Include filepaths for source and include.
include( mqttFilePaths.cmake )

set(MODULE_NAME "mqtt")

# MQTT library target.
module(NAME ${MODULE_NAME} INTERFACE)

set_lib_metadata(ID ${MODULE_NAME})
set_lib_metadata(DESCRIPTION "This library implements the MQTT 3.1.1 protocol that enables \
communication with AWS IoT. MQTT is an ISO standard publish-subscribe-based messaging protocol.")
set_lib_metadata(DISPLAY_NAME "MQTTv4_beta2")
set_lib_metadata(CATEGORY "Connectivity")
set_lib_metadata(VERSION "1.0.0")
set_lib_metadata(IS_VISIBLE "true")

module_sources(
    ${MODULE_NAME}
    PRIVATE
        ${MQTT_SOURCES}
)

# MQTT include paths.
module_include_dirs(${MODULE_NAME} 
                       PRIVATE 
                        ${MQTT_INCLUDE_PRIVATE_DIRS} 
                        ${LOGGING_INCLUDE_DIRS}
                       PUBLIC
                        ${MQTT_INCLUDE_PUBLIC_DIRS})

if(DEFINED AFR_IS_TESTING)
    set(BUILD_TESTS ${AFR_IS_TESTING})
endif()

if(${BUILD_TESTS})
    add_subdirectory( utest )
    add_subdirectory( integration-test )
endif()
