# MQTT tests executable.
add_executable( aws_iot_tests_mqtt
                aws_iot_tests_mqtt.c
                ${CMAKE_SOURCE_DIR}/tests/aws_iot_tests_network.c
                unit/aws_iot_tests_mqtt_api.c
                unit/aws_iot_tests_mqtt_receive.c
                unit/aws_iot_tests_mqtt_subscription.c
                unit/aws_iot_tests_mqtt_validate.c
                system/aws_iot_tests_mqtt_system.c
                system/aws_iot_tests_mqtt_stress.c )

# MQTT tests library dependencies.
target_link_libraries( aws_iot_tests_mqtt awsiotcommon awsiotplatform awsiotmqtt unity )
