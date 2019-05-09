# MQTT library source files.
set( MQTT_SOURCES
     iot_mqtt_api.c
     iot_mqtt_network.c
     iot_mqtt_operation.c
     iot_mqtt_serialize.c
     iot_mqtt_static_memory.c
     iot_mqtt_subscription.c
     iot_mqtt_validate.c )

# MQTT library target.
add_library( iotmqtt
             ${MQTT_SOURCES}
             ${PROJECT_SOURCE_DIR}/lib/include/iot_mqtt.h
             ${PROJECT_SOURCE_DIR}/lib/include/types/iot_mqtt_types.h
             ${PROJECT_SOURCE_DIR}/lib/include/private/iot_mqtt_internal.h )

# Link required libraries.
target_link_libraries( iotmqtt iotcommon iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotmqtt unity )
endif()

# Organization of MQTT in folders.
set_property( TARGET iotmqtt PROPERTY FOLDER "lib" )
source_group( include FILES ${PROJECT_SOURCE_DIR}/lib/include/iot_mqtt.h )
source_group( include\\types FILES ${PROJECT_SOURCE_DIR}/lib/include/types/iot_mqtt_types.h )
source_group( include\\private FILES ${PROJECT_SOURCE_DIR}/lib/include/private/iot_mqtt_internal.h )
source_group( source FILES ${MQTT_SOURCES} )
