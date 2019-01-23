# MQTT library source files.
add_library( awsiotmqtt SHARED
             aws_iot_mqtt_api.c
             aws_iot_mqtt_operation.c
             aws_iot_mqtt_serialize.c
             aws_iot_mqtt_subscription.c
             aws_iot_mqtt_validate.c )

# Library version.
set_target_properties( awsiotmqtt PROPERTIES VERSION ${PROJECT_VERSION} )

# Library public headers.
set_target_properties( awsiotmqtt PROPERTIES PUBLIC_HEADER
                       "../../include/aws_iot_mqtt.h" )

# Library private headers.
set_target_properties( awsiotmqtt PROPERTIES PRIVATE_HEADER
                       "../../include/private/aws_iot_mqtt_internal.h" )

# Link required libraries.
target_link_libraries( awsiotmqtt awsiotcommon awsiotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotmqtt unity )
endif()
