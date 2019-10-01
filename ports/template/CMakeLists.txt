# This CMakeLists is a template for new ports. It provides the minimal
# configuration for building, but nothing more.

# Warn that the template port only builds. It will not create usable libraries.
message( WARNING "This is a template port that contains only stubs. Libraries built with this port will not work!")

# Add the mbed TLS header in the template. The mbed TLS network port is supposed
# to be platform-independent, so it is built in the template.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_mbedtls.h
     PARENT_SCOPE )

# Template platform sources. Except for the network sources, these files contain
# only stubs.
set( PLATFORM_SOURCES
     # Stubs
     ${CMAKE_SOURCE_DIR}/platform/ports/template/source/iot_clock_template.c
     ${CMAKE_SOURCE_DIR}/platform/ports/template/source/iot_threads_template.c

     # Network sources
     ${CMAKE_SOURCE_DIR}/platform/network/iot_network_mbedtls.c
     ${CMAKE_SOURCE_DIR}/platform/network/iot_network_metrics.c )

# ANYTHING BELOW THIS LINE TYPICALLY DOES NOT NEED TO BE MODIFIED.

# Add platform as an interface library. It will be built into iotbase.
add_library( iotplatform INTERFACE )

target_sources( iotplatform INTERFACE
                ${PLATFORM_SOURCES} )

# This template platform layer uses mbed TLS, since it builds the mbed TLS network
# sources.
target_link_libraries( iotplatform INTERFACE mbedtls )

# Set platform sources in the parent scope for directory organization.
set( PLATFORM_SOURCES ${PLATFORM_SOURCES} PARENT_SCOPE )
