# Common unit test sources.
set( COMMON_UNIT_TEST_SOURCES
     unit/iot_tests_linear_containers.c
     unit/iot_tests_taskpool.c
     unit/iot_tests_atomic.c )

# Common tests executable.
add_executable( iot_tests_common
                ${COMMON_UNIT_TEST_SOURCES}
                iot_tests_common.c
                ${PROJECT_SOURCE_DIR}/tests/iot_config.h )

# Common tests library dependencies.
target_link_libraries( iot_tests_common PRIVATE iotcommon unity )

# Organization of common tests in folders.
set_property( TARGET iot_tests_common PROPERTY FOLDER "tests" )
source_group( unit FILES ${COMMON_UNIT_TEST_SOURCES} )
source_group( "" FILES iot_tests_common.c ${PROJECT_SOURCE_DIR}/tests/iot_config.h )
