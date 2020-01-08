# Shadow library source files.
set( SHADOW_SOURCES
     src/aws_iot_shadow_api.c
     src/aws_iot_shadow_operation.c
     src/aws_iot_shadow_parser.c
     src/aws_iot_shadow_static_memory.c
     src/aws_iot_shadow_subscription.c )

# Shadow library target.
add_library( awsiotshadow
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${SHADOW_SOURCES}
             include/aws_iot_shadow.h
             include/types/aws_iot_shadow_types.h
             src/private/aws_iot_shadow_internal.h )

# Shadow public include path.
target_include_directories( awsiotshadow PUBLIC include )

# Link required libraries.
target_link_libraries( awsiotshadow PRIVATE awsiotcommon iotserializer iotbase )

# Shadow is currently implemented on MQTT, so link MQTT as a public dependency.
target_link_libraries( awsiotshadow PUBLIC iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotshadow PRIVATE unity )
endif()

# Organization of Shadow in folders.
set_property( TARGET awsiotshadow PROPERTY FOLDER libraries/aws )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot_shadow.h )
source_group( include\\types include/types/aws_iot_shadow_types.h )
source_group( src\\private src/private/aws_iot_shadow_internal.h )
source_group( src FILES ${SHADOW_SOURCES} )

# Install the library with public headers.
install(TARGETS awsiotshadow
        LIBRARY
        DESTINATION lib
        ARCHIVE
        DESTINATION lib)

install(FILES include/aws_iot_shadow.h
        DESTINATION include/aws_iot/)

install(FILES include/types/aws_iot_shadow_types.h
        DESTINATION include/aws_iot/types)

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Shadow system test sources.
    set( SHADOW_SYSTEM_TEST_SOURCES
         test/system/aws_iot_tests_shadow_system.c )

    # Shadow unit test sources.
    set( SHADOW_UNIT_TEST_SOURCES
         test/unit/aws_iot_tests_shadow_api.c
         test/unit/aws_iot_tests_shadow_parser.c )

    # Shadow tests executable.
    add_executable( aws_iot_tests_shadow
                    ${SHADOW_SYSTEM_TEST_SOURCES}
                    ${SHADOW_UNIT_TEST_SOURCES}
                    test/aws_iot_tests_shadow.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_shadow PRIVATE
                                -DRunTests=RunShadowTests )

    # The Shadow tests need the internal Shadow header.
    target_include_directories( aws_iot_tests_shadow PRIVATE src )

    # Shadow tests library dependencies.
    target_link_libraries( aws_iot_tests_shadow PRIVATE
                           awsiotshadow awsiotcommon iotserializer iotbase
                           unity iot_mqtt_mock )

    # Organization of Shadow tests in folders.
    set_property( TARGET aws_iot_tests_shadow PROPERTY FOLDER tests )
    source_group( system FILES ${SHADOW_SYSTEM_TEST_SOURCES} )
    source_group( unit FILES ${SHADOW_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/aws_iot_tests_shadow.c )
endif()
