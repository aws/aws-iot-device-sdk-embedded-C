# MQTT system test sources.
set( MQTT_SYSTEM_TEST_SOURCES
     system/iot_tests_mqtt_system.c )

# MQTT unit test sources.
set( MQTT_UNIT_TEST_SOURCES
     unit/iot_tests_mqtt_api.c
     unit/iot_tests_mqtt_receive.c
     unit/iot_tests_mqtt_subscription.c
     unit/iot_tests_mqtt_validate.c )

# MQTT tests executable.
add_executable( iot_tests_mqtt
                ${MQTT_SYSTEM_TEST_SOURCES}
                ${MQTT_UNIT_TEST_SOURCES}
                ${IOT_TEST_APP_FILES} )

# Define the test to run.
target_compile_definitions( iot_tests_mqtt PRIVATE
                            -DIOT_TEST_MQTT=1 )

# MQTT tests library dependencies.
target_link_libraries( iot_tests_mqtt PRIVATE iotmqtt unity )

# Organization of MQTT tests in folders.
set_property( TARGET iot_tests_mqtt PROPERTY FOLDER "tests" )
source_group( system FILES ${MQTT_SYSTEM_TEST_SOURCES} )
source_group( unit FILES ${MQTT_UNIT_TEST_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} )
