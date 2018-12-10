# Shadow library source files.
add_library( awsiotshadow SHARED
             aws_iot_shadow_api.c
             aws_iot_shadow_operation.c
             aws_iot_shadow_parser.c
             aws_iot_shadow_subscription.c )

# Library version.
set_target_properties( awsiotshadow PROPERTIES VERSION ${PROJECT_VERSION} )

# Library public headers.
set_target_properties( awsiotshadow PROPERTIES PUBLIC_HEADER
                       "../../include/aws_iot_shadow.h" )

# Library private headers.
set_target_properties( awsiotmqtt PROPERTIES PRIVATE_HEADER
                       "../../include/private/aws_iot_shadow_internal.h" )

# Link required libraries.
target_link_libraries( awsiotshadow awsiotcommon awsiotplatform awsiotmqtt )

# Link Unity test framework when building tests.
if( ${AWS_IOT_BUILD_TESTS} )
    target_link_libraries( awsiotshadow unity )
endif()
