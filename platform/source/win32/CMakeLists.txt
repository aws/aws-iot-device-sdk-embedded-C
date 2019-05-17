# Add the network header for this platform.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_mbedtls.h
     PARENT_SCOPE )

# Platform library source files.
set( PLATFORM_SOURCES
     ${CMAKE_SOURCE_DIR}/platform/source/win32/iot_clock_win32.c
     ${CMAKE_SOURCE_DIR}/platform/source/win32/iot_threads_win32.c
     ${CMAKE_SOURCE_DIR}/platform/source/network/iot_network_mbedtls.c
     ${CMAKE_SOURCE_DIR}/platform/source/network/iot_network_metrics.c
     PARENT_SCOPE )

# This platform layer uses mbed TLS.
set( IOT_BASE_DEPENDENCIES ${IOT_BASE_DEPENDENCIES} mbedtls PARENT_SCOPE )
