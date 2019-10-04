# Add the network header for this platform.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${CMAKE_SOURCE_DIR}/ports/common/include/iot_network_mbedtls.h )

# Platform library source files.
set( PLATFORM_SOURCES
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_clock_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_threads_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/common/src/iot_network_mbedtls.c
     ${PORTS_DIRECTORY}/common/src/iot_network_metrics.c )

# Set the types header for this port.
set( PORT_TYPES_HEADER ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/include/iot_platform_types_${IOT_PLATFORM_NAME}.h )

# Set the dependencies required by this port.
# On Windows, mbed TLS and Winsock are used.
set( PLATFORM_DEPENDENCIES mbedtls ws2_32 )
