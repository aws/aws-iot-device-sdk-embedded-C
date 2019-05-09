# Shadow library source files.
set( SHADOW_SOURCES
     aws_iot_shadow_api.c
     aws_iot_shadow_operation.c
     aws_iot_shadow_parser.c
     aws_iot_shadow_static_memory.c
     aws_iot_shadow_subscription.c )

# Shadow library target.
add_library( awsiotshadow
             ${SHADOW_SOURCES}
             ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_shadow.h
             ${PROJECT_SOURCE_DIR}/lib/include/types/aws_iot_shadow_types.h
             ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_shadow_internal.h )

# Link required libraries.
target_link_libraries( awsiotshadow iotserializer iotplatform iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotshadow unity )
endif()

# Organization of Shadow in folders.
set_property( TARGET awsiotshadow PROPERTY FOLDER "lib" )
source_group( include FILES ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_shadow.h )
source_group( include\\types ${PROJECT_SOURCE_DIR}/lib/include/types/aws_iot_shadow_types.h )
source_group( include\\private ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_shadow_internal.h )
source_group( source FILES ${SHADOW_SOURCES} )
