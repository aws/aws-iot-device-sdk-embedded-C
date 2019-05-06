# Shadow library source files.
add_library( awsiotshadow
             aws_iot_shadow_api.c
             aws_iot_shadow_operation.c
             aws_iot_shadow_parser.c
             aws_iot_shadow_static_memory.c
             aws_iot_shadow_subscription.c )

# Library version.
set_target_properties( awsiotshadow PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( awsiotshadow iotserializer iotplatform iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotshadow unity )
endif()
