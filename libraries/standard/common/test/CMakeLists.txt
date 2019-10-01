# Common unit test sources.
set( COMMON_UNIT_TEST_SOURCES
     unit/iot_tests_linear_containers.c
     unit/iot_tests_taskpool.c
     unit/iot_tests_atomic.c )

# Common tests executable.
add_executable( iot_tests_common
                ${COMMON_UNIT_TEST_SOURCES}
                iot_tests_common.c
                ${IOT_TEST_APP_FILES} )

# Define the test to run.
target_compile_definitions( iot_tests_common PRIVATE
                            -DRunTests=RunCommonTests )

# Common tests library dependencies.
target_link_libraries( iot_tests_common PRIVATE iotbase unity )

# Organization of common tests in folders.
set_property( TARGET iot_tests_common PROPERTY FOLDER "tests" )
source_group( unit FILES ${COMMON_UNIT_TEST_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} iot_tests_common.c )
