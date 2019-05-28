include( CheckCCompilerFlag )
include( CheckTypeSize )
include( CheckFunctionExists )

# Check that the -lrt flag works.
check_c_compiler_flag( -lrt HAS_C_FLAG_lrt )

if( NOT HAS_C_FLAG_lrt )
    message( FATAL_ERROR "Compiler flag -lrt must be supported." )
endif()

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
        set( NETWORK_HEADER ${CMAKE_SOURCE_DIR}/platform/include/iot_network_openssl.h )
        set( NETWORK_SOURCE_FILE ${CMAKE_SOURCE_DIR}/platform/ports/posix/source/iot_network_openssl.c )

        # Link OpenSSL.
        set( TLS_LIBRARY_LINKER_FLAG OpenSSL::SSL OpenSSL::Crypto )
    endif()
else()
    set( NETWORK_HEADER ${CMAKE_SOURCE_DIR}/platform/include/iot_network_mbedtls.h )
    set( NETWORK_SOURCE_FILE ${CMAKE_SOURCE_DIR}/platform/network/iot_network_mbedtls.c )
    set( TLS_LIBRARY_LINKER_FLAG mbedtls )
endif()

# Add the network header for this platform.
set( PLATFORM_COMMON_HEADERS ${PLATFORM_COMMON_HEADERS}
     ${NETWORK_HEADER}
     PARENT_SCOPE )

# Platform libraries source files.
set( PLATFORM_SOURCES
     ${CMAKE_SOURCE_DIR}/platform/ports/posix/source/iot_clock_posix.c
     ${CMAKE_SOURCE_DIR}/platform/ports/posix/source/iot_threads_posix.c
     ${CMAKE_SOURCE_DIR}/platform/network/iot_network_metrics.c
     ${NETWORK_SOURCE_FILE} )

# Add platform as an interface library. It will be built into iotbase.
add_library( iotplatform INTERFACE )

target_sources( iotplatform INTERFACE
                ${PLATFORM_SOURCES} )

# Set the dependencies of this platform layer.
target_link_libraries( iotplatform INTERFACE Threads::Threads rt ${TLS_LIBRARY_LINKER_FLAG} )

# Set platform sources in the parent scope for directory organization.
set( PLATFORM_SOURCES ${PLATFORM_SOURCES} PARENT_SCOPE )
