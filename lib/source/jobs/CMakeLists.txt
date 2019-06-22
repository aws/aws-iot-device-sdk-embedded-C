# Jobs library source files.
set( JOBS_SOURCES
     aws_iot_jobs_api.c
     aws_iot_jobs_serialize.c
     aws_iot_jobs_operation.c
     aws_iot_jobs_static_memory.c
     aws_iot_jobs_subscription.c )

# Jobs library target.
add_library( awsiotjobs
             ${JOBS_SOURCES}
             ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_jobs.h
             ${PROJECT_SOURCE_DIR}/lib/include/types/aws_iot_jobs_types.h
             ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_jobs_internal.h )

# Link required libraries.
target_link_libraries( awsiotjobs PUBLIC awsiotcommon )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotjobs PRIVATE unity )
endif()

# Organization of Jobs in folders.
set_property( TARGET awsiotjobs PROPERTY FOLDER "lib" )
source_group( include FILES ${PROJECT_SOURCE_DIR}/lib/include/aws_iot_jobs.h )
source_group( include\\types ${PROJECT_SOURCE_DIR}/lib/include/types/aws_iot_jobs_types.h )
source_group( include\\private ${PROJECT_SOURCE_DIR}/lib/include/private/aws_iot_jobs_internal.h )
source_group( source FILES ${JOBS_SOURCES} )
