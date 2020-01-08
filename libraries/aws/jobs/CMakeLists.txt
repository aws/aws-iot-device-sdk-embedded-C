# Jobs library source files.
set( JOBS_SOURCES
     src/aws_iot_jobs_api.c
     src/aws_iot_jobs_serialize.c
     src/aws_iot_jobs_operation.c
     src/aws_iot_jobs_static_memory.c
     src/aws_iot_jobs_subscription.c )

# Jobs library target.
add_library( awsiotjobs
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${JOBS_SOURCES}
             include/aws_iot_jobs.h
             include/types/aws_iot_jobs_types.h
             src/private/aws_iot_jobs_internal.h )

# Jobs public include path.
target_include_directories( awsiotjobs PUBLIC include )

# Link required libraries.
target_link_libraries( awsiotjobs PRIVATE awsiotcommon iotserializer iotbase )

# Jobs is currently implemented on MQTT, so link MQTT as a public dependency.
target_link_libraries( awsiotjobs PUBLIC iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotjobs PRIVATE unity )
endif()

# Organization of Jobs in folders.
set_property( TARGET awsiotjobs PROPERTY FOLDER libraries/aws )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot_jobs.h )
source_group( include\\types include/types/aws_iot_jobs_types.h )
source_group( src\\private src/private/aws_iot_jobs_internal.h )
source_group( src FILES ${JOBS_SOURCES} )

# Install the library with public headers.
install(TARGETS awsiotjobs
        LIBRARY
        DESTINATION lib
        ARCHIVE
        DESTINATION lib)

install(FILES include/aws_iot_jobs.h
            include/types/aws_iot_jobs_types.h
        DESTINATION include/aws_iot/)

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Jobs system test sources.
    set( JOBS_SYSTEM_TEST_SOURCES
         test/system/aws_iot_tests_jobs_system.c )

    # Jobs unit test sources.
    set( JOBS_UNIT_TEST_SOURCES
         test/unit/aws_iot_tests_jobs_api.c
         test/unit/aws_iot_tests_jobs_serialize.c )

    # Jobs tests executable.
    add_executable( aws_iot_tests_jobs
                    ${JOBS_SYSTEM_TEST_SOURCES}
                    ${JOBS_UNIT_TEST_SOURCES}
                    test/aws_iot_tests_jobs.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_jobs PRIVATE
                                -DRunTests=RunJobsTests )

    # The Jobs tests need the internal Jobs header.
    target_include_directories( aws_iot_tests_jobs PRIVATE src )

    # Jobs tests library dependencies.
    target_link_libraries( aws_iot_tests_jobs PRIVATE
                           awsiotjobs awsiotcommon iotserializer iotbase
                           unity iot_mqtt_mock )

    # Organization of Jobs tests in folders.
    set_property( TARGET aws_iot_tests_jobs PROPERTY FOLDER tests )
    source_group( system FILES ${JOBS_SYSTEM_TEST_SOURCES} )
    source_group( unit FILES ${JOBS_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/aws_iot_tests_jobs.c )
endif()
