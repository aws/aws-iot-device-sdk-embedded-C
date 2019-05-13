# Defender system test sources.
set( DEFENDER_SYSTEM_TEST_SOURCES
     system/aws_iot_tests_defender_system.c )

# Defender tests executable.
add_executable( aws_iot_tests_defender
                ${DEFENDER_SYSTEM_TEST_SOURCES}
                ${IOT_TEST_APP_FILES} )

# Define the test to run.
target_compile_definitions( aws_iot_tests_defender PRIVATE
                            -DAWS_IOT_TEST_DEFENDER=1 )

# Defender tests library dependencies.
target_link_libraries( aws_iot_tests_defender PRIVATE awsiotdefender tinycbor unity )

# Organization of Defender tests in folders.
set_property( TARGET aws_iot_tests_defender PROPERTY FOLDER "tests" )
source_group( system FILES ${DEFENDER_SYSTEM_TEST_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} )
