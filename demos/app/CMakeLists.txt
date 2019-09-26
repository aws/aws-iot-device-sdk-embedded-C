# Common demo source files.
set( DEMO_COMMON_SOURCES
     iot_demo.c
     iot_demo_arguments.c )

# When testing the demos, add the test sources and redefine the demo main function.
if( ${IOT_BUILD_TESTS} )
    list( APPEND DEMO_COMMON_SOURCES ${PROJECT_SOURCE_DIR}/tests/iot_tests.c )
    set_property( SOURCE iot_demo.c PROPERTY COMPILE_DEFINITIONS main=DemoMain )
    set_property( SOURCE ${PROJECT_SOURCE_DIR}/tests/iot_tests.c PROPERTY COMPILE_DEFINITIONS IOT_TEST_DEMO=1 )
    set( CONFIG_HEADER ${PROJECT_SOURCE_DIR}/tests/iot_config.h )
else()
    set( CONFIG_HEADER ${PROJECT_SOURCE_DIR}/demos/iot_config.h )
endif()

# Common demo header files.
set( DEMO_COMMON_HEADERS
     ${PROJECT_SOURCE_DIR}/demos/include/iot_demo_arguments.h
     ${PROJECT_SOURCE_DIR}/demos/include/iot_demo_logging.h )

# MQTT demo source files.
add_executable( iot_demo_mqtt
                ${PROJECT_SOURCE_DIR}/demos/source/iot_demo_mqtt.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS}
                ${CONFIG_HEADER} )

# Select the demo function for the MQTT demo.
target_compile_definitions( iot_demo_mqtt
                            PRIVATE RunDemo=RunMqttDemo )

# MQTT demo library dependencies.
target_link_libraries( iot_demo_mqtt PRIVATE iotmqtt )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iot_demo_mqtt PRIVATE unity )
endif()

# Organization of MQTT demo in folders.
set_property( TARGET iot_demo_mqtt PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/iot_demo_mqtt.c
              ${CONFIG_HEADER} )

# Shadow demo source files.
add_executable( aws_iot_demo_shadow
                ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_shadow.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS}
                ${CONFIG_HEADER} )

# Select the demo function for the Shadow demo.
target_compile_definitions( aws_iot_demo_shadow
                            PRIVATE RunDemo=RunShadowDemo )

# Shadow demo library dependencies.
target_link_libraries( aws_iot_demo_shadow PRIVATE awsiotshadow )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( aws_iot_demo_shadow PRIVATE unity )
endif()

# Organization of Shadow demo in folders.
set_property( TARGET aws_iot_demo_shadow PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_shadow.c
              ${CONFIG_HEADER} )

# Defender demo source files.
add_executable( aws_iot_demo_defender
                ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_defender.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS}
                ${CONFIG_HEADER} )

# Select the demo function for the Defender demo.
target_compile_definitions( aws_iot_demo_defender
                            PRIVATE RunDemo=RunDefenderDemo )

# Defender demo library dependencies.
target_link_libraries( aws_iot_demo_defender PRIVATE awsiotdefender )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( aws_iot_demo_defender PRIVATE unity )
endif()

# Organization of the Defender demo in folders.
set_property( TARGET aws_iot_demo_defender PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_defender.c
              ${CONFIG_HEADER} )

# Jobs demo source files.
add_executable( aws_iot_demo_jobs
                ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_jobs.c
                ${DEMO_COMMON_SOURCES}
                ${DEMO_COMMON_HEADERS}
                ${CONFIG_HEADER} )

# Select the demo function for the Jobs demo.
target_compile_definitions( aws_iot_demo_jobs
                            PRIVATE RunDemo=RunJobsDemo )

# Jobs demo library dependencies.
target_link_libraries( aws_iot_demo_jobs PRIVATE awsiotjobs )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( aws_iot_demo_jobs PRIVATE unity )
endif()

# Organization of the Jobs demo in folders.
set_property( TARGET aws_iot_demo_jobs PROPERTY FOLDER "demos" )
source_group( include FILES ${DEMO_COMMON_HEADERS} )
source_group( "" FILES ${DEMO_COMMON_SOURCES}
              ${PROJECT_SOURCE_DIR}/demos/source/aws_iot_demo_jobs.c
              ${CONFIG_HEADER} )
