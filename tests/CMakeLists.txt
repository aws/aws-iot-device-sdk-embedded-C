# Test runner executable and config header.
set( IOT_TEST_APP_FILES
     ${PROJECT_SOURCE_DIR}/tests/iot_config.h
     ${PROJECT_SOURCE_DIR}/tests/iot_tests.c )

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
