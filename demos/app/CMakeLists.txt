# Source file for parsing arguments.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    set( DEMO_ARGUMENTS_SOURCE_FILE posix/iot_demo_arguments_posix.c )
endif()

# Common demo source files.
set( DEMO_COMMON_SOURCES
     ${DEMO_ARGUMENTS_SOURCE_FILE}
     iot_demo.c )

# Common demo header files.
set( DEMO_COMMON_HEADERS
     ${PROJECT_SOURCE_DIR}/demos/include/iot_demo_arguments.h
     ${PROJECT_SOURCE_DIR}/demos/include/iot_demo_logging.h )

# MQTT demo source files.
add_executable( iot_demo_mqtt
                ${PROJECT_SOURCE_DIR}/demos/source/iot_demo_mqtt.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS} )

# Select the demo function for the MQTT demo.
target_compile_definitions( iot_demo_mqtt
                            PRIVATE RunDemo=RunMqttDemo )

# MQTT demo library dependencies.
target_link_libraries( iot_demo_mqtt PRIVATE iotmqtt )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iot_demo_mqtt PRIVATE unity )
endif()

# Organization of MQTT demo in folders.
set_property( TARGET iot_demo_mqtt PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/iot_demo_mqtt.c )

# Shadow demo source files.
add_executable( aws_iot_demo_shadow
                ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_shadow.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS} )

# Select the demo function for the Shadow demo.
target_compile_definitions( aws_iot_demo_shadow
                            PRIVATE RunDemo=RunShadowDemo )

# Shadow demo library dependencies.
target_link_libraries( aws_iot_demo_shadow PRIVATE awsiotshadow )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( aws_iot_demo_shadow PRIVATE unity )
endif()

# Organization of Shadow demo in folders.
set_property( TARGET aws_iot_demo_shadow PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_shadow.c )
