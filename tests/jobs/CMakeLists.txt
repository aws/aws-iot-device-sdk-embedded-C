# Jobs unit test sources.
set( JOBS_UNIT_TEST_SOURCES
     system/aws_iot_tests_jobs_system.c
     unit/aws_iot_tests_jobs_api.c
     unit/aws_iot_tests_jobs_serialize.c )

# Jobs tests executable.
add_executable( aws_iot_tests_jobs
                ${JOBS_UNIT_TEST_SOURCES}
                aws_iot_tests_jobs.c
                ${IOT_TEST_APP_FILES}
                ${MQTT_MOCK_SOURCES} )

# Include directory for MQTT mock.
target_include_directories( aws_iot_tests_jobs PRIVATE
                            ${PROJECT_SOURCE_DIR}/tests/mqtt/mock )

# Define the test to run.
target_compile_definitions( aws_iot_tests_jobs PRIVATE
                            -DRunTests=RunJobsTests )

# Jobs tests library dependencies.
target_link_libraries( aws_iot_tests_jobs PRIVATE awsiotjobs unity )

# Organization of Jobs tests in folders.
set_property( TARGET aws_iot_tests_jobs PROPERTY FOLDER "tests" )
source_group( unit FILES ${JOBS_UNIT_TEST_SOURCES} )
source_group( mock FILES ${MQTT_MOCK_SOURCES} )
source_group( "" FILES ${IOT_TEST_APP_FILES} aws_iot_tests_jobs.c )
