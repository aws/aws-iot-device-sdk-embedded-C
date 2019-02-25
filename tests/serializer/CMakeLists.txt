# Shadow tests executable.
add_executable( iot_tests_serializer
                iot_tests_serializer.c
                iot_test_serializer_cbor.c )

# Shadow tests library dependencies.
target_link_libraries( iot_tests_serializer iotcommon iotplatform iotserializer unity )