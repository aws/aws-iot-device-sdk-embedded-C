# PROVISIONING library source files.
set( PROVISIONING_SOURCES
     src/aws_iot_provisioning_api.c
     src/aws_iot_provisioning_parser.c
     src/aws_iot_provisioning_serializer.c )

# PROVISIONING library target.
add_library( awsiotprovisioning
            # ${CONFIG_HEADER_PATH}/iot_config.h
             ${PROVISIONING_SOURCES}
             include/aws_iot_provisioning.h
             include/types/aws_iot_provisioning_types.h
             src/private/aws_iot_provisioning_internal.h )

# Provisioning public include path.
target_include_directories( awsiotprovisioning PUBLIC include )

# Provisioning private include path.
target_include_directories( awsiotprovisioning PRIVATE src )

# Link required libraries.
target_link_libraries( awsiotprovisioning PRIVATE awsiotcommon iotbase iotserializer )

# Jobs is currently implemented on MQTT, so link MQTT as a public dependency.
target_link_libraries( awsiotprovisioning PUBLIC iotmqtt )

# Organization of PROVISIONING in folders.
set_property( TARGET awsiotprovisioning PROPERTY FOLDER "lib" )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot_provisioning.h )
source_group( include\\types FILES include/types/aws_iot_provisioning_types.h )
source_group( include\\private FILES src/private/aws_iot_provisioning_internal.h )
source_group( source FILES ${PROVISIONING_SOURCES} )

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Link Unity test framework when building tests.
    target_link_libraries( awsiotprovisioning PRIVATE unity )
    
    # Provisioning unit test sources.
    set( PROVISIONING_UNIT_TEST_SOURCES
         test/unit/aws_iot_tests_provisioning_api.c
         test/unit/aws_iot_tests_provisioning_serializer.c
         test/unit/aws_iot_tests_provisioning_parser.c )
    
    # Provisioning unit test sources.
    set( PROVISIONING_SYSTEM_TEST_SOURCES
         test/system/aws_iot_tests_provisioning_system.c )

    # Provisioning tests executable.
    add_executable( aws_iot_tests_provisioning
                    ${PROVISIONING_UNIT_TEST_SOURCES}
                    ${PROVISIONING_SYSTEM_TEST_SOURCES}
                    test/aws_iot_tests_provisioning.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )
    
    # Include directory for Provisioning and MQTT libraries' private files.
    target_include_directories( aws_iot_tests_provisioning PRIVATE
                                src
                                ${PROJECT_SOURCE_DIR}/libraries/standard/mqtt/src)

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_provisioning PRIVATE
                                -DRunTests=RunProvisioningTests )

    # Provisioning tests library dependencies.
    target_link_libraries( aws_iot_tests_provisioning PRIVATE 
                           awsiotprovisioning 
                           awsiotcommon
                           unity 
                           iot_mqtt_mock 
                           iotbase
                           iotserializer)

    # Organization of Provisioning tests in folders.
    set_property( TARGET aws_iot_tests_provisioning PROPERTY FOLDER "tests" )
    source_group( unit FILES ${PROVISIONING_UNIT_TEST_SOURCES} )
    source_group( system FILES ${PROVISIONING_SYSTEM_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} aws_iot_tests_provisioning.c )

endif()