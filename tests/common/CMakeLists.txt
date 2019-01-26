# Common tests executable.
add_executable( iot_tests_common
                iot_tests_common.c
                unit/iot_tests_linear_containers.c )

# Common tests library dependencies.
target_link_libraries( iot_tests_common unity iotcommon )
