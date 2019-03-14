# Serializer library source files.
add_library( iotserializer SHARED
             cbor/iot_serializer_tinycbor_decoder.c
             cbor/iot_serializer_tinycbor_encoder.c )

# Library version.
set_target_properties( iotserializer PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( iotserializer tinycbor )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotserializer unity )
endif()