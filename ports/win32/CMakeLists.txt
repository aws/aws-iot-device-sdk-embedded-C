# Add the network header for this platform.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_mbedtls.h
     PARENT_SCOPE )

# Platform library source files.
set( PLATFORM_SOURCES
     ${CMAKE_SOURCE_DIR}/platform/ports/win32/source/iot_clock_win32.c
     ${CMAKE_SOURCE_DIR}/platform/ports/win32/source/iot_threads_win32.c
     ${CMAKE_SOURCE_DIR}/platform/network/iot_network_mbedtls.c
     ${CMAKE_SOURCE_DIR}/platform/network/iot_network_metrics.c )

# Add platform as an interface library. It will be built into iotbase.
add_library( iotplatform INTERFACE )

target_sources( iotplatform INTERFACE
                ${PLATFORM_SOURCES} )

# This platform layer uses mbed TLS.
target_link_libraries( iotplatform INTERFACE mbedtls )

# Link the Winsock2 library.
target_link_libraries( iotplatform INTERFACE ws2_32 )

# Set platform sources in the parent scope for directory organization.
set( PLATFORM_SOURCES ${PLATFORM_SOURCES} PARENT_SCOPE )
