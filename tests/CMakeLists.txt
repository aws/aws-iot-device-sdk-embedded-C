# Test runner executable and config header.
set( IOT_TEST_APP_FILES
     ${PROJECT_SOURCE_DIR}/tests/iot_config.h
     ${PROJECT_SOURCE_DIR}/tests/iot_tests.c )

# MQTT mock sources.
set( MQTT_MOCK_SOURCES
    ${PROJECT_SOURCE_DIR}/tests/mqtt/mock/iot_tests_mqtt_mock.c
    ${PROJECT_SOURCE_DIR}/tests/mqtt/mock/iot_tests_mqtt_mock.h )

# Common tests.
add_subdirectory( common )

# Defender tests.
add_subdirectory( defender )

# MQTT tests.
add_subdirectory( mqtt )

# Serializer tests.
add_subdirectory( serializer )

# Shadow tests.
add_subdirectory( shadow )

# Jobs tests.
add_subdirectory( jobs )
