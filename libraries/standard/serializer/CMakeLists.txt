# Serializer library source files.
set( SERIALIZER_SOURCES
     src/iot_serializer_static_memory.c
     src/cbor/iot_serializer_tinycbor_decoder.c
     src/cbor/iot_serializer_tinycbor_encoder.c )

# Serializer library target.
add_library( iotserializer
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${SERIALIZER_SOURCES}
             include/iot_serializer.h )

# Serializer public include path.
target_include_directories( iotserializer PUBLIC include )

# Link required libraries.
target_link_libraries( iotserializer PRIVATE iotbase tinycbor )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotserializer PRIVATE unity )
endif()

# Organization of Serializer in folders.
set_property( TARGET iotserializer PROPERTY FOLDER libraries/standard )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( include FILES
              include/iot_serializer.h )
source_group( src FILES ${SERIALIZER_SOURCES} )

# Install the library with public headers.
include( ${PROJECT_SOURCE_DIR}/ports/install_${IOT_PLATFORM_NAME}/${IOT_PLATFORM_NAME}.cmake
        OPTIONAL RESULT_VARIABLE INSTALL_FUNC_FOUND )

if ( INSTALL_FUNC_FOUND )
    InstallBinary( iotserializer )
    InstallHeaders( include/iot_serializer.h aws_iot )
endif()

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Serializer unit test sources.
    set( SERIALIZER_UNIT_TEST_SOURCES
         test/unit/iot_tests_serializer_cbor.c )

    # Serializer tests executable.
    add_executable( iot_tests_serializer
                    ${SERIALIZER_UNIT_TEST_SOURCES}
                    test/iot_tests_serializer.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( iot_tests_serializer PRIVATE
                                -DRunTests=RunSerializerTests )

    # Serializer tests library dependencies.
    target_link_libraries( iot_tests_serializer PRIVATE iotserializer iotbase unity tinycbor )

    # Organization of serializer tests in folders.
    set_property( TARGET iot_tests_serializer PROPERTY FOLDER tests )
    source_group( unit FILES ${SERIALIZER_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/iot_tests_serializer.c )
endif()
