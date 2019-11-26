# This CMakeLists is a template for new ports. It provides the minimal
# configuration for building, but nothing more.

# Warn that the template port only builds. It will not create usable libraries.
message( WARNING "This is a template port that contains only stubs. Libraries built with this port will not work!")

# Add the mbed TLS header in the template. The mbed TLS network port is supposed
# to be platform-independent, so it is built in the template.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${PORTS_DIRECTORY}/common/include/iot_network_mbedtls.h )

# Template platform sources. Except for the network sources, these files contain
# only stubs.
set( PLATFORM_SOURCES
     # Stubs
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_clock_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_threads_${IOT_PLATFORM_NAME}.c )

# Set the types header for this port.
set( PORT_TYPES_HEADER ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/include/iot_platform_types_${IOT_PLATFORM_NAME}.h )

# Set the dependencies required by this port.
# As this template uses the mbed TLS network implementation, mbed TLS is linked.
set( PLATFORM_DEPENDENCIES mbedtls )
