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

# Propagate values to compiler flags, even if they are not defined.
target_compile_definitions(
    ${DEMO_NAME} PRIVATE
        ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
        AWS_IOT_ENDPOINT="${AWS_IOT_ENDPOINT}"
        CLIENT_CERT_PATH="${CLIENT_CERT_PATH}"
        CLIENT_PRIVATE_KEY_PATH="${CLIENT_PRIVATE_KEY_PATH}"
)
