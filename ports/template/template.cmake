# This CMakeLists is a template for new ports. It provides the minimal
# configuration for building, but nothing more.

# Warn that the template port only builds. It will not create usable libraries.
message( WARNING "This is a template port that contains only stubs. Libraries built with this port will not work!")

# Add the template network header.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${PORTS_DIRECTORY}/common/include/iot_network_template.h )

# Template platform sources.
set( PLATFORM_SOURCES
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_clock_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_threads_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_network_${IOT_PLATFORM_NAME}.c )

# Set the types header for this port.
set( PORT_TYPES_HEADER ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/include/iot_platform_types_${IOT_PLATFORM_NAME}.h )
