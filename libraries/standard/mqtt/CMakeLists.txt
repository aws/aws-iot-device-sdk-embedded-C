# MQTT library source files.
set( MQTT_SOURCES
     src/iot_mqtt_api.c
     src/iot_mqtt_network.c
     src/iot_mqtt_operation.c
     src/iot_mqtt_serialize.c
     src/iot_mqtt_static_memory.c
     src/iot_mqtt_subscription.c
     src/iot_mqtt_validate.c )

set( MQTT_PUBLIC_HEADERS
        include/iot_mqtt.h
        include/iot_mqtt_serialize.h)
set( MQTT_PRIVATE_HEADERS
        src/private/iot_mqtt_internal.h )
set( MQTT_TYPES_HEADERS
        include/types/iot_mqtt_types.h )

# MQTT library target.
add_library( iotmqtt
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${MQTT_SOURCES}
             ${MQTT_PUBLIC_HEADERS}
             ${MQTT_PRIVATE_HEADERS}
             ${MQTT_TYPES_HEADERS} )

# MQTT public include path.
target_include_directories( iotmqtt PUBLIC include )

# Link required libraries.
target_link_libraries( iotmqtt PRIVATE iotbase )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotmqtt PRIVATE unity )
endif()

# Organization of MQTT in folders.
set_property( TARGET iotmqtt PROPERTY FOLDER libraries/standard )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/iot_mqtt.h )
source_group( include\\types FILES include/types/iot_mqtt_types.h )
source_group( src FILES ${MQTT_SOURCES} )
source_group( src\\private FILES src/private/iot_mqtt_internal.h )

# Install the library with public headers.
install(TARGETS iotmqtt
        LIBRARY
        DESTINATION lib
        ARCHIVE
        DESTINATION lib)

install(FILES ${MQTT_PUBLIC_HEADERS}
        DESTINATION include/aws_iot/)

install(FILES ${MQTT_TYPES_HEADERS}
        DESTINATION include/aws_iot/types)

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Enable test access in MQTT.
    target_compile_definitions( iotmqtt PRIVATE -DIOT_BUILD_TESTS=1 )
    target_include_directories( iotmqtt PUBLIC test/access )

    # This test library is used to mock MQTT connections.
    add_library( iot_mqtt_mock
                 test/mock/iot_tests_mqtt_mock.c
                 test/mock/iot_tests_mqtt_mock.h
                 ${CONFIG_HEADER_PATH}/iot_config.h )

    # Organization of MQTT mock library in folders.
    set_property( TARGET iot_mqtt_mock PROPERTY FOLDER tests )
    source_group( "" FILES
                  test/mock/iot_tests_mqtt_mock.c
                  test/mock/iot_tests_mqtt_mock.h
                  ${CONFIG_HEADER_PATH}/iot_config.h )

    # The MQTT mock needs the internal MQTT header.
    target_include_directories( iot_mqtt_mock
                                PRIVATE src
                                PUBLIC test/mock )

    # Link required libraries for MQTT mock.
    target_link_libraries( iot_mqtt_mock PRIVATE iotbase iotmqtt unity )

    # MQTT system test sources.
    set( MQTT_SYSTEM_TEST_SOURCES
         test/system/iot_tests_mqtt_system.c )

    # MQTT unit test sources.
    set( MQTT_UNIT_TEST_SOURCES
         test/unit/iot_tests_mqtt_api.c
         test/unit/iot_tests_mqtt_receive.c
         test/unit/iot_tests_mqtt_subscription.c
         test/unit/iot_tests_mqtt_validate.c )

    # MQTT tests executable.
    add_executable( iot_tests_mqtt
                    ${MQTT_SYSTEM_TEST_SOURCES}
                    ${MQTT_UNIT_TEST_SOURCES}
                    test/iot_tests_mqtt.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( iot_tests_mqtt PRIVATE
                                -DRunTests=RunMqttTests )

    # The MQTT tests need the internal MQTT header.
    target_include_directories( iot_tests_mqtt PRIVATE src )

    # MQTT tests library dependencies.
    target_link_libraries( iot_tests_mqtt PRIVATE iotmqtt iotbase unity iot_mqtt_mock )

    # Organization of MQTT tests in folders.
    set_property( TARGET iot_tests_mqtt PROPERTY FOLDER tests )
    source_group( system FILES ${MQTT_SYSTEM_TEST_SOURCES} )
    source_group( unit FILES ${MQTT_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/iot_tests_mqtt.c )
endif()
