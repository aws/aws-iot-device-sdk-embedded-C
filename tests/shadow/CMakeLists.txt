# Shadow tests executable.
add_executable( aws_iot_tests_shadow
                aws_iot_tests_shadow.c
                ${CMAKE_SOURCE_DIR}/tests/iot_tests_network.c
                unit/aws_iot_tests_shadow_api.c
                unit/aws_iot_tests_shadow_parser.c
                system/aws_iot_tests_shadow_system.c )

# Shadow tests library dependencies.
target_link_libraries( aws_iot_tests_shadow iotcommon iotplatform iotmqtt awsiotshadow unity )
