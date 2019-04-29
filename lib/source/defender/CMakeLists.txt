# Serializer library source files.
add_library( awsiotdefender
             aws_iot_defender_api.c
             aws_iot_defender_collector.c
             aws_iot_defender_mqtt.c )

# Library version.
set_target_properties( awsiotdefender PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( awsiotdefender iotserializer iotmqtt iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotdefender unity )
endif()
