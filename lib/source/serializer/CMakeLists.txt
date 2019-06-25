# Serializer library source files.
set( SERIALIZER_SOURCES
     iot_json_utils.c
     iot_serializer_static_memory.c
     cbor/iot_serializer_tinycbor_decoder.c
     cbor/iot_serializer_tinycbor_encoder.c )

# Serializer library target.
add_library( iotserializer
             ${SERIALIZER_SOURCES}
             ${PROJECT_SOURCE_DIR}/lib/include/iot_serializer.h
             ${PROJECT_SOURCE_DIR}/lib/include/iot_json_utils.h )

# Link required libraries.
target_link_libraries( iotserializer PRIVATE iotbase tinycbor )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotserializer PRIVATE unity )
endif()

# Organization of Serializer in folders.
set_property( TARGET iotserializer PROPERTY FOLDER "lib" )
source_group( include FILES
              ${PROJECT_SOURCE_DIR}/lib/include/iot_serializer.h
              ${PROJECT_SOURCE_DIR}/lib/include/iot_json_utils.h )
source_group( source FILES ${SERIALIZER_SOURCES} )
