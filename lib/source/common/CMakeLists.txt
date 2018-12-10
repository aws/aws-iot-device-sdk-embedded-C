# Common libraries source files.
add_library( awsiotcommon SHARED
             aws_iot_json_utils.c
             aws_iot_logging.c
             aws_iot_queue.c )

# Library version.
set_target_properties( awsiotcommon PROPERTIES VERSION ${PROJECT_VERSION} )

# Library public headers.
set_target_properties( awsiotcommon PROPERTIES PUBLIC_HEADER
                       "../../include/aws_iot_json_utils.h;../../include/aws_iot_logging_setup.h;../../include/aws_iot_queue.h" )

# Library private headers.
set_target_properties( awsiotcommon PROPERTIES PRIVATE_HEADER
                       "../../include/private/aws_iot_logging.h" )

# Link required libraries.
target_link_libraries( awsiotcommon awsiotplatform )

# Link Unity test framework when building tests.
if( ${AWS_IOT_BUILD_TESTS} )
    target_link_libraries( awsiotcommon unity )
endif()
