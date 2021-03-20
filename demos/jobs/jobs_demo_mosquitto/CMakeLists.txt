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
    message( "Mosquitto was not installed. It will be built from source to run ${DEMO_NAME}." )
    # Build Mosquitto Client Library from source if it is not installed.
    add_subdirectory( libmosquitto )
    target_link_libraries(
        ${DEMO_NAME}
        PUBLIC
            libmosquitto
    )
    # Exclude extraneous mosquitto targets.
    set_target_properties(mosquittopp PROPERTIES EXCLUDE_FROM_ALL true)
    set_target_properties(mosquitto_rr PROPERTIES EXCLUDE_FROM_ALL true)
    set_target_properties(mosquitto_sub PROPERTIES EXCLUDE_FROM_ALL true)
    set_target_properties(mosquitto_pub PROPERTIES EXCLUDE_FROM_ALL true)
    set_target_properties(mosquitto_passwd PROPERTIES EXCLUDE_FROM_ALL true)
    set_target_properties(mosquitto PROPERTIES EXCLUDE_FROM_ALL true)

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

set_macro_definitions(TARGETS ${DEMO_NAME}
                      OPTIONAL
                        "AWS_IOT_ENDPOINT"
                        "ROOT_CA_CERT_PATH"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                    )
