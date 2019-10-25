include( CheckTypeSize )
include( CheckFunctionExists )

# Check that the POSIX realtime library is available.
find_library( LIB_REALTIME rt )

if( ${LIB_REALTIME} STREQUAL "LIB_REALTIME-NOTFOUND" )
    message( FATAL_ERROR "POSIX realtime library (librt) is not available." )
endif()

unset( LIB_REALTIME CACHE )

# Check for POSIX threads.
find_package( Threads REQUIRED )

if( NOT ${CMAKE_USE_PTHREADS_INIT} )
    message( FATAL_ERROR "POSIX threads required." )
endif()

# Check for required POSIX types.
set( CMAKE_EXTRA_INCLUDE_FILES "pthread.h" "time.h" "semaphore.h" )
list( APPEND REQUIRED_POSIX_TYPES
      pthread_t
      pthread_attr_t
      pthread_mutex_t
      sem_t
      timer_t  )

foreach( POSIX_TYPE ${REQUIRED_POSIX_TYPES} )
    check_type_size( ${POSIX_TYPE} SIZEOF_${POSIX_TYPE} )

    if( NOT HAVE_SIZEOF_${POSIX_TYPE} )
        message( FATAL_ERROR "Required type ${POSIX_TYPE} not found." )
    endif()
endforeach()

# Check for some required POSIX functions. This is not intended to be a comprehensive list.
set( CMAKE_REQUIRED_LIBRARIES rt Threads::Threads )
list( APPEND REQUIRED_POSIX_FUNCTIONS
      clock_gettime time localtime_r strftime timer_create timer_delete
      timer_settime pthread_create pthread_attr_init pthread_attr_setdetachstate
      pthread_mutex_init pthread_mutex_lock pthread_mutex_trylock pthread_mutex_unlock
      sem_init sem_getvalue sem_wait sem_trywait sem_timedwait sem_post )

foreach( POSIX_FUNCTION ${REQUIRED_POSIX_FUNCTIONS} )
    check_function_exists( ${POSIX_FUNCTION} HAVE_${POSIX_FUNCTION} )

    if( NOT HAVE_${POSIX_FUNCTION} )
        message( FATAL_ERROR "Required function ${POSIX_FUNCTION} not found." )
    endif()
endforeach()

# Choose either OpenSSL or mbed TLS.
if( ${IOT_NETWORK_USE_OPENSSL} )
    # Check for OpenSSL.
    find_package( OpenSSL )

    # Minimum supported OpenSSL version is 1.0.2g.
    if( ${OPENSSL_FOUND} )
        if( ${OPENSSL_VERSION} STRLESS "1.0.2g" )
            message( FATAL_ERROR "OpenSSL 1.0.2g or later required, found ${OPENSSL_VERSION}." )
        endif()

        # Choose OpenSSL network source file.
        set( NETWORK_HEADER ${PORTS_DIRECTORY}/common/include/iot_network_openssl.h )
        set( NETWORK_SOURCE_FILE ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_network_openssl.c )

        # Link OpenSSL.
        set( PLATFORM_DEPENDENCIES OpenSSL::SSL OpenSSL::Crypto )
    endif()
else()
    set( NETWORK_HEADER ${PORTS_DIRECTORY}/common/include/iot_network_openssl.h )
    set( NETWORK_SOURCE_FILE ${PORTS_DIRECTORY}/common/src/iot_network_mbedtls.c )
    set( PLATFORM_DEPENDENCIES mbedtls )
    set( MBEDTLS_REQUIRED TRUE PARENT_SCOPE )
endif()

# Add the network header for this platform.
list( APPEND PLATFORM_COMMON_HEADERS
     ${NETWORK_HEADER} )

# Platform libraries source files.
set( PLATFORM_SOURCES
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_clock_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/src/iot_threads_${IOT_PLATFORM_NAME}.c
     ${PORTS_DIRECTORY}/common/src/iot_network_metrics.c
     ${NETWORK_SOURCE_FILE} )

# Set the types header for this port.
set( PORT_TYPES_HEADER ${PORTS_DIRECTORY}/${IOT_PLATFORM_NAME}/include/iot_platform_types_${IOT_PLATFORM_NAME}.h )

# Link POSIX threads and real-time library.
set( PLATFORM_DEPENDENCIES ${PLATFORM_DEPENDENCIES} Threads::Threads rt )
