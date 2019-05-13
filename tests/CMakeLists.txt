# Test runner executable and config header.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    set( IOT_TEST_APP_FILES
         ${PROJECT_SOURCE_DIR}/tests/app/iot_tests_posix.c
         ${PROJECT_SOURCE_DIR}/tests/iot_config.h )
endif()

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
