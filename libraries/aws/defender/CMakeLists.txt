# Defender library source files.
set( DEFENDER_SOURCES
     src/aws_iot_defender_api.c
     src/aws_iot_defender_collector.c
     src/aws_iot_defender_mqtt.c )

# Defender library target.
add_library( awsiotdefender
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${DEFENDER_SOURCES}
             include/aws_iot_defender.h
             src/private/aws_iot_defender_internal.h )

# Defender public include path.
target_include_directories( awsiotdefender PUBLIC include )

# Link required libraries.
target_link_libraries( awsiotdefender PRIVATE awsiotcommon iotserializer iotbase )

# Defender is currently implemented on MQTT, so link MQTT as a public dependency.
target_link_libraries( awsiotdefender PUBLIC iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotdefender PRIVATE unity )
endif()

# Organization of Defender in folders.
set_property( TARGET awsiotdefender PROPERTY FOLDER libraries/aws )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot_defender.h )
source_group( src\\private src/private/aws_iot_defender_internal.h )
source_group( src FILES ${DEFENDER_SOURCES} )

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Defender system test sources.
    set( DEFENDER_SYSTEM_TEST_SOURCES
         test/unit/aws_iot_tests_defender_unit.c
         test/system/aws_iot_tests_defender_system.c )

    # Defender tests executable.
    add_executable( aws_iot_tests_defender
                    ${DEFENDER_SYSTEM_TEST_SOURCES}
                    test/aws_iot_tests_defender.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_defender PRIVATE
                                -DRunTests=RunDefenderTests )

    # The Defender tests need the internal Defender header.
    target_include_directories( aws_iot_tests_defender PRIVATE src )

    # Defender tests library dependencies.
    target_link_libraries( aws_iot_tests_defender PRIVATE
                           awsiotdefender awsiotcommon iotserializer iotbase
                           unity tinycbor iot_mqtt_mock )

    # Organization of Defender tests in folders.
    set_property( TARGET aws_iot_tests_defender PROPERTY FOLDER tests )
    source_group( system FILES ${DEFENDER_SYSTEM_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/aws_iot_tests_defender.c )
endif()
