# Common demo files.
set( DEMO_COMMON_SOURCE_FILES
     iot_demo_arguments_posix.c
     iot_demo_posix.c )

# MQTT demo source files.
add_executable( iot_demo_mqtt
                ${CMAKE_SOURCE_DIR}/demos/source/iot_demo_mqtt.c
                ${DEMO_COMMON_SOURCE_FILES} )

# Select the demo function for the MQTT demo.
target_compile_definitions( iot_demo_mqtt
                            PRIVATE RunDemo=RunMqttDemo )

# MQTT demo library dependencies.
target_link_libraries( iot_demo_mqtt iotplatform iotmqtt )

# Shadow demo source files.
add_executable( aws_iot_demo_shadow
                ${CMAKE_SOURCE_DIR}/demos/source/aws_iot_demo_shadow.c
                ${DEMO_COMMON_SOURCE_FILES} )

# Select the demo function for the Shadow demo.
target_compile_definitions( aws_iot_demo_shadow
                            PRIVATE RunDemo=RunShadowDemo )

# Shadow demo library dependencies.
target_link_libraries( aws_iot_demo_shadow iotplatform iotmqtt awsiotshadow )
