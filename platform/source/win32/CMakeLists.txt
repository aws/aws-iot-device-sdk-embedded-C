# Platform interface headers.
set( PLATFORM_INTERFACE_HEADERS
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_clock.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_metrics.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_network.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_threads.h )

# Platform types headers.
set( PLATFORM_TYPES_HEADERS
     ${CMAKE_SOURCE_DIR}/lib/include/types/iot_platform_types.h
     ${CMAKE_SOURCE_DIR}/platform/include/win32/iot_platform_types_win32.h )

# Platform common headers.
set( PLATFORM_COMMON_HEADERS
     ${CMAKE_SOURCE_DIR}/platform/include/iot_atomic.h
     ${CMAKE_SOURCE_DIR}/platform/include/atomic/iot_atomic_generic.h
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_mbedtls.h
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_metrics.h )

# Platform library source files.
set( PLATFORM_SOURCES
     iot_clock_win32.c
     iot_threads_win32.c
     ${CMAKE_SOURCE_DIR}/platform/source/network/iot_network_mbedtls.c
     ${CMAKE_SOURCE_DIR}/platform/source/network/iot_network_metrics.c )

# Platform library target.
add_library( iotplatform
             ${PLATFORM_SOURCES}
             ${PLATFORM_INTERFACE_HEADERS}
             ${PLATFORM_TYPES_HEADERS}
             ${PLATFORM_COMMON_HEADERS} )

# Link required libraries.
target_link_libraries( iotplatform PRIVATE mbedtls )

# Organization of platform in folders.
source_group( interface FILES ${PLATFORM_INTERFACE_HEADERS} )
source_group( include\\types FILES ${PLATFORM_TYPES_HEADERS} )
source_group( include FILES ${PLATFORM_COMMON_HEADERS} )
source_group( source FILES ${PLATFORM_SOURCES} )
