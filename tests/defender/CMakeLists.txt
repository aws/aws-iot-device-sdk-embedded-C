# Defender system test sources.
set( DEFENDER_SYSTEM_TEST_SOURCES
     system/aws_iot_tests_defender_system.c )

# Defender tests executable.
add_executable( aws_iot_tests_defender
                ${DEFENDER_SYSTEM_TEST_SOURCES}
                aws_iot_tests_defender.c
                ${PROJECT_SOURCE_DIR}/tests/iot_config.h )

# Defender tests library dependencies.
target_link_libraries( aws_iot_tests_defender PRIVATE awsiotdefender unity )

# Organization of Defender tests in folders.
set_property( TARGET aws_iot_tests_defender PROPERTY FOLDER "tests" )
source_group( system FILES ${DEFENDER_SYSTEM_TEST_SOURCES} )
source_group( "" FILES aws_iot_tests_defender.c ${PROJECT_SOURCE_DIR}/tests/iot_config.h )
