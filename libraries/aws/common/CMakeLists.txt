# AWS IoT common library source files.
set( AWS_IOT_COMMON_SOURCES
     src/aws_iot_doc_parser.c
     src/aws_iot_operation.c
     src/aws_iot_parser.c
     src/aws_iot_subscription.c
     src/aws_iot_validate.c )

set( AWS_IOT_COMMON_PUBLIC_HEADERS
        include/aws_iot.h
        include/aws_iot_doc_parser.h)

# AWS IoT common library target.
add_library( awsiotcommon
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${AWS_IOT_COMMON_SOURCES}
             ${AWS_IOT_COMMON_PUBLIC_HEADERS} )

# AWS IoT common public include path.
target_include_directories( awsiotcommon PUBLIC include )

# Link required libraries.
target_link_libraries( awsiotcommon PRIVATE iotbase iotmqtt )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( awsiotcommon PRIVATE unity )
endif()

# Organization of AWS IoT common in folders.
set_property( TARGET awsiotcommon PROPERTY FOLDER libraries/aws )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES include/aws_iot.h include/aws_iotdoc_parser.h )
source_group( src FILES ${AWS_IOT_COMMON_SOURCES} )

# Install the library with public headers.
include( ${PROJECT_SOURCE_DIR}/ports/install_${IOT_PLATFORM_NAME}/${IOT_PLATFORM_NAME}.cmake
         OPTIONAL RESULT_VARIABLE INSTALL_FUNC_FOUND )

if ( INSTALL_FUNC_FOUND )
    InstallBinary( awsiotcommon )
    InstallHeaders( AWS_IOT_COMMON_PUBLIC_HEADERS aws_iot )
endif()


# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # AWS IoT Common unit test sources.
    set( AWS_IOT_COMMON_UNIT_TEST_SOURCES
         test/unit/aws_iot_tests_doc_parser.c )

    # AWS IoT Common tests executable.
    add_executable( aws_iot_tests_common
                    ${AWS_IOT_COMMON_UNIT_TEST_SOURCES}
                    test/aws_iot_tests_common.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( aws_iot_tests_common PRIVATE
                                -DRunTests=RunAwsIotCommonTests )

    # AWS IoT Common tests library dependencies.
    target_link_libraries( aws_iot_tests_common PRIVATE awsiotcommon iotbase unity )

    # Organization of AWS IoT Common tests in folders.
    set_property( TARGET aws_iot_tests_common PROPERTY FOLDER tests )
    source_group( unit FILES ${AWS_IOT_COMMON_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/aws_iot_tests_common.c )
endif()