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

find_library(LIB_MOSQUITTO mosquitto)
if(${LIB_MOSQUITTO} STREQUAL "LIB_MOSQUITTO-NOTFOUND")
    message( "Mosquitto was not installed. It will be built from source for ${DEMO_NAME}." )
    # Build Mosquitto Client Library from source if it is not installed.
    add_subdirectory( libmosquitto )
    target_link_libraries(
    ${DEMO_NAME}
    PUBLIC
        libmosquitto
    )
    target_include_directories(
        ${DEMO_NAME}
        SYSTEM PUBLIC
            ${CMAKE_CURRENT_LIST_DIR}/libmosquitto/lib
    )
else()
    target_link_libraries(
    ${DEMO_NAME}
    PUBLIC
        mosquitto
    )
endif()

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        ${JOBS_INCLUDE_PUBLIC_DIRS}
        ${JSON_INCLUDE_PUBLIC_DIRS}
)

if(AWS_IOT_ENDPOINT)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            AWS_IOT_ENDPOINT="${AWS_IOT_ENDPOINT}"
    )
endif()
if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(CLIENT_CERT_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            CLIENT_CERT_PATH="${CLIENT_CERT_PATH}"
    )
endif()
if(CLIENT_PRIVATE_KEY_PATH)
    target_compile_definitions(
        ${DEMO_NAME} PRIVATE
            CLIENT_PRIVATE_KEY_PATH="${CLIENT_PRIVATE_KEY_PATH}"
    )
endif()
