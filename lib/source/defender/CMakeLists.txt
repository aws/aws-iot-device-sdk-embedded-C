# Defender library source files.
set( DEFENDER_SOURCES
     aws_iot_defender_api.c
     aws_iot_defender_collector.c
     aws_iot_defender_mqtt.c )

# Defender library target.
add_library( awsiotdefender
             ${DEFENDER_SOURCES}
             ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_defender.h
             ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_defender_internal.h )

# Link required libraries.
target_link_libraries( awsiotdefender PUBLIC iotserializer iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotdefender PRIVATE unity )
endif()

# Organization of Defender in folders.
set_property( TARGET awsiotdefender PROPERTY FOLDER "lib" )
source_group( include FILES ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_defender.h )
source_group( include\\private ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_defender_internal.h )
source_group( source FILES ${DEFENDER_SOURCES} )
