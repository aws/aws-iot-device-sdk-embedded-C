set( DEMO_NAME "jobs_demo_mosquitto" )

# The callbacks for libmosquitto have parameters that are not used.
set_source_files_properties( "${DEMO_NAME}.c" PROPERTIES COMPILE_FLAGS "-Wno-unused-parameter" )

# Include library source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreJSON/jsonFilePaths.cmake )
include( ${CMAKE_SOURCE_DIR}/libraries/aws/jobs-for-aws-iot-embedded-sdk/jobsFilePaths.cmake )

# Demo target.
add_executable(
    ${DEMO_NAME}
        "${DEMO_NAME}.c"
        ${JOBS_SOURCES}
        ${JSON_SOURCES}
)

check_aws_credentials(${DEMO_NAME})

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mosquitto
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${JOBS_INCLUDE_PUBLIC_DIRS}
        ${JSON_INCLUDE_PUBLIC_DIRS}
)
