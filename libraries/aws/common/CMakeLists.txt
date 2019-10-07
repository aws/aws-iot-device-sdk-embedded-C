# AWS IoT common library source files.
set( AWS_IOT_COMMON_SOURCES
     src/aws_iot_operation.c
     src/aws_iot_parser.c
     src/aws_iot_subscription.c
     src/aws_iot_validate.c )

# AWS IoT common library target.
add_library( awsiotcommon
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${AWS_IOT_COMMON_SOURCES}
             include/aws_iot.h )

# AWS IoT common public include path.
target_include_directories( awsiotcommon PUBLIC include )

# Link required libraries.
target_link_libraries( awsiotcommon PRIVATE iotbase iotmqtt iotserializer )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotcommon PRIVATE unity )
endif()

# Organization of AWS IoT common in folders.
set_property( TARGET awsiotcommon PROPERTY FOLDER libraries/aws )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot.h )
source_group( src FILES ${AWS_IOT_COMMON_SOURCES} )
