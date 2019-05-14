# Serializer unit test sources.
set( SERIALIZER_UNIT_TEST_SOURCES
     unit/iot_tests_serializer_cbor.c )

# Serializer tests executable.
add_executable( iot_tests_serializer
                ${SERIALIZER_UNIT_TEST_SOURCES}
                iot_tests_serializer.c
                ${IOT_TEST_APP_FILES} )

# Define the test to run.
target_compile_definitions( iot_tests_serializer PRIVATE
                            -DRunTests=RunSerializerTests )

# Serializer tests library dependencies.
target_link_libraries( iot_tests_serializer PRIVATE iotserializer iotcommon unity tinycbor )

# Organization of Serializer tests in folders.
set_property( TARGET iot_tests_serializer PROPERTY FOLDER "tests" )
source_group( unit FILES ${SERIALIZER_UNIT_TEST_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} iot_tests_serializer.c )
