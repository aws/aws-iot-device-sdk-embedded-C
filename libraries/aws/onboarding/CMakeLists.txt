# ONBOARDING library source files.
set( ONBOARDING_SOURCES
     src/aws_iot_onboarding_api.c
     src/aws_iot_onboarding_parser.c
     src/aws_iot_onboarding_serializer.c )

# ONBOARDING library target.
add_library( awsiotonboarding
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${ONBOARDING_SOURCES}
             include/aws_iot_onboarding.h
             include/types/aws_iot_onboarding_types.h
             src/private/aws_iot_onboarding_internal.h )

# Onboarding public include path.
target_include_directories( awsiotonboarding PUBLIC include )

# Onboarding private include path.
target_include_directories( awsiotonboarding PRIVATE src )

# Link required libraries.
target_link_libraries( awsiotonboarding PRIVATE awsiotcommon iotbase iotserializer )

# Jobs is currently implemented on MQTT, so link MQTT as a public dependency.
target_link_libraries( awsiotonboarding PUBLIC iotmqtt )

# Organization of ONBOARDING in folders.
set_property( TARGET awsiotonboarding PROPERTY FOLDER "lib" )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot_onboarding.h )
source_group( include\\types FILES include/types/aws_iot_onboarding_types.h )
source_group( include\\private FILES src/private/aws_iot_onboarding_internal.h )
source_group( source FILES ${ONBOARDING_SOURCES} )

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Link Unity test framework when building tests.
    target_link_libraries( awsiotonboarding PRIVATE unity )
    
    # Onboarding unit test sources.
    set( ONBOARDING_UNIT_TEST_SOURCES
         test/unit/aws_iot_tests_onboarding_api.c
         test/unit/aws_iot_tests_onboarding_serializer.c )
    
    # Onboarding unit test sources.
    set( ONBOARDING_SYSTEM_TEST_SOURCES
         test/system/aws_iot_tests_onboarding_system.c )

    # Onboarding tests executable.
    add_executable( aws_iot_tests_onboarding
                    ${ONBOARDING_UNIT_TEST_SOURCES}
                    ${ONBOARDING_SYSTEM_TEST_SOURCES}
                    test/aws_iot_tests_onboarding.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )
    
    # Include directory for Onboarding and MQTT libraries' private files.
    target_include_directories( aws_iot_tests_onboarding PRIVATE
                                src
                                ${PROJECT_SOURCE_DIR}/libraries/standard/mqtt/src)

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_onboarding PRIVATE
                                -DRunTests=RunOnboardingTests )

    # Onboarding tests library dependencies.
    target_link_libraries( aws_iot_tests_onboarding PRIVATE 
                           awsiotonboarding 
                           unity iot_mqtt_mock 
                           iotbase
                           iotserializer)

    # Organization of Onboarding tests in folders.
    set_property( TARGET aws_iot_tests_onboarding PROPERTY FOLDER "tests" )
    source_group( unit FILES ${ONBOARDING_UNIT_TEST_SOURCES} )
    source_group( system FILES ${ONBOARDING_SYSTEM_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} aws_iot_tests_onboarding.c )

endif()