set( DEMO_NAME "jobs_demo_mosquitto" )

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
