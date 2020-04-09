# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# MQTT library source files.
set( MQTT_SOURCES
     src/iot_mqtt_api.c
     src/iot_mqtt_network.c
     src/iot_mqtt_operation.c
     src/iot_mqtt_serialize.c
     src/iot_mqtt_lightweight_api.c
     src/iot_mqtt_helper.c
     src/iot_mqtt_static_memory.c
     src/iot_mqtt_subscription.c
     src/iot_mqtt_validate.c )

# MQTT library Include directories.
set( MQTT_INCLUDE_PUBLIC_DIRS
     include )

# MQTT system test source files.
set( MQTT_SYSTEM_TEST_SOURCES
     test/system/iot_tests_mqtt_system.c )

# MQTT unit test sources.
set( MQTT_UNIT_TEST_SOURCES
     test/unit/iot_tests_mqtt_api.c
     test/unit/iot_tests_mqtt_receive.c
     test/unit/iot_tests_mqtt_subscription.c
     test/unit/iot_tests_mqtt_validate.c )

# MQTT test include directories.
set( MQTT_TEST_INCLUDE_PRIVATE_DIRS
     src )

# MQTT mock source files.
set( MQTT_TEST_MOCK_SOURCES
     test/mock/iot_tests_mqtt_mock.c )

# MQTT mock include directories.
set( MQTT_TEST_MOCK_INCLUDE_PRIVATE_DIRS
     src )
set( MQTT_TEST_MOCK_INCLUDE_PUBLIC_DIRS
     test/mock )