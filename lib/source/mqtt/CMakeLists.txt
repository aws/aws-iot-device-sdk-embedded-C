# MQTT library source files.
add_library( iotmqtt SHARED
             iot_mqtt_api.c
             iot_mqtt_network.c
             iot_mqtt_operation.c
             iot_mqtt_serialize.c
             iot_mqtt_subscription.c
             iot_mqtt_validate.c )

# Library version.
set_target_properties( iotmqtt PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( iotmqtt iotcommon iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotmqtt unity )
endif()
