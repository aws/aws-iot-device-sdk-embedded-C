# MQTT tests executable.
add_executable( iot_tests_mqtt
                iot_tests_mqtt.c
                ${CMAKE_SOURCE_DIR}/tests/iot_tests_network.c
                unit/iot_tests_mqtt_api.c
                unit/iot_tests_mqtt_receive.c
                unit/iot_tests_mqtt_subscription.c
                unit/iot_tests_mqtt_validate.c
                system/iot_tests_mqtt_system.c
                system/iot_tests_mqtt_stress.c )

# MQTT tests library dependencies.
target_link_libraries( iot_tests_mqtt iotcommon iotplatform iotmqtt unity )
