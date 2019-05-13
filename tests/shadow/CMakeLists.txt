# Shadow system test sources.
set( SHADOW_SYSTEM_TEST_SOURCES
     system/aws_iot_tests_shadow_system.c )

# Shadow unit test sources.
set( SHADOW_UNIT_TEST_SOURCES
     unit/aws_iot_tests_shadow_api.c
     unit/aws_iot_tests_shadow_parser.c )

# Shadow tests executable.
add_executable( aws_iot_tests_shadow
                ${SHADOW_SYSTEM_TEST_SOURCES}
                ${SHADOW_UNIT_TEST_SOURCES}
                ${IOT_TEST_APP_FILES} )

# Define the test to run.
target_compile_definitions( aws_iot_tests_shadow PRIVATE
                            -DAWS_IOT_TEST_SHADOW=1 )

# Shadow tests library dependencies.
target_link_libraries( aws_iot_tests_shadow PRIVATE awsiotshadow unity )

# Organization of Shadow tests in folders.
set_property( TARGET aws_iot_tests_shadow PROPERTY FOLDER "tests" )
source_group( system FILES ${SHADOW_SYSTEM_TEST_SOURCES} )
source_group( unit FILES ${SHADOW_UNIT_TEST_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} )
