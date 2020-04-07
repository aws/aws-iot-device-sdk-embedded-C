# This file is to populate source files and include directories
# into a variables so that it can be reused.

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

# MQTT system test sources.
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