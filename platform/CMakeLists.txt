# For static library builds, link against static library of OpenSSL
if(NOT BUILD_SHARED_LIBS)
    set( OPENSSL_USE_STATIC_LIBS TRUE )
endif()
find_package(OpenSSL)
# Verify the minimum OpenSSL version required
if( ${OPENSSL_FOUND} AND ( OPENSSL_VERSION MATCHES "0.9$" OR OPENSSL_VERSION MATCHES "1.0$" ) )
    message( WARNING "OpenSSL 1.1.0 or later required: OpenSSL ${OPENSSL_VERSION} found." )
endif()

set(OpenSSL_FOUND ${OpenSSL_FOUND} CACHE INTERNAL "Indicates whether OpenSSL library was found.")

if( NOT DEFINED LIB_RT_NAME )
    set( LIB_RT_NAME "rt" CACHE STRING "Name of the POSIX.1b Realtime Extensions library." )
endif()

find_library(LIB_RT ${LIB_RT_NAME})


# Add the posix targets
add_subdirectory( ${PLATFORM_DIR}/posix )

# Add ota porting targets
add_subdirectory( ${PLATFORM_DIR}/posix/ota_pal )
