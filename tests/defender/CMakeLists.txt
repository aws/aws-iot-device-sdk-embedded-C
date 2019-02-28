# Defender tests executable.
add_executable( aws_iot_tests_defender
                aws_iot_tests_defender.c
                aws_iot_tests_defender_api.c )

# Defender tests library dependencies.
target_link_libraries( aws_iot_tests_defender iotcommon iotplatform iotmqtt awsiotdefender unity )

# Not produce warning on missing braces case.
target_compile_options( aws_iot_tests_defender PRIVATE "-Wno-missing-braces")