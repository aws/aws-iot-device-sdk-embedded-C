# Common demo files.
set( DEMO_COMMON_INCLUDE_FILES ".;${CMAKE_SOURCE_DIR}/demos" )
set( DEMO_COMMON_SOURCE_FILES iot_demo_common_posix.c )

# MQTT demo source files.
add_executable( iot_demo_mqtt
                ${CMAKE_SOURCE_DIR}/demos/iot_demo_mqtt.c
                iot_demo_mqtt_posix.c
                ${DEMO_COMMON_SOURCE_FILES} )

# MQTT demo include files.
target_include_directories( iot_demo_mqtt
                            PRIVATE
                            ${DEMO_COMMON_INCLUDE_FILES} )

# MQTT demo library dependencies.
target_link_libraries( iot_demo_mqtt iotplatform iotmqtt )

# Shadow demo source files.
add_executable( aws_iot_demo_shadow
                ${CMAKE_SOURCE_DIR}/demos/aws_iot_demo_shadow.c
                aws_iot_demo_shadow_posix.c
                ${DEMO_COMMON_SOURCE_FILES} )

# Shadow demo include files.
target_include_directories( iot_demo_mqtt
                            PRIVATE
                            ${DEMO_COMMON_INCLUDE_FILES} )

# Shadow demo library dependencies.
target_link_libraries( aws_iot_demo_shadow iotplatform iotmqtt awsiotshadow )
