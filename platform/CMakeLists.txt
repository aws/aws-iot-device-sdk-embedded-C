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

if(VXWORKS)
    # VxWorks does not provide a separate librt library.
    # All POSIX defined librt APIs are provided in libc instead.
    find_library(LIB_RT c)
else()
    find_library(LIB_RT rt)
endif()

# Add the posix targets
add_subdirectory( ${PLATFORM_DIR}/posix )

# Add ota porting targets
add_subdirectory( ${PLATFORM_DIR}/posix/ota_pal )
