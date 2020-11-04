# Include filepaths for source and include.
include( ${PLATFORM_DIR}/posix/posixFilePaths.cmake )

set( TRANSPORT_INTERFACE_INCLUDE_DIR
     ${MODULES_DIR}/standard/coreMQTT/source/interface )

# Create target for sockets utility.
add_library( sockets_posix
                ${SOCKETS_SOURCES} )

target_include_directories( sockets_posix
                            PUBLIC
                                ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
                                ${LOGGING_INCLUDE_DIRS}
                                ${TRANSPORT_INTERFACE_INCLUDE_DIR} )

# Create target for plaintext transport.
add_library( plaintext_posix
             ${PLAINTEXT_TRANSPORT_SOURCES} )

target_link_libraries( plaintext_posix
                       PUBLIC
                           sockets_posix )

# Create target for POSIX implementation of OpenSSL.
add_library( openssl_posix
                ${OPENSSL_TRANSPORT_SOURCES} )

# For static library builds, link against static library of OpenSSL
# for openssl_posix target.
if(NOT BUILD_SHARED_LIBS)
    set( OPENSSL_USE_STATIC_LIBS TRUE )
endif()
find_package( OpenSSL REQUIRED )

# Verify the minimum OpenSSL version required
if( OPENSSL_VERSION MATCHES "0.9$" OR OPENSSL_VERSION MATCHES "1.0$"  )
    message( FATAL_ERROR "OpenSSL 1.1.0 or later required: OpenSSL ${OPENSSL_VERSION} found." )
endif()

set( CMAKE_THREAD_PREFER_PTHREAD ON )
find_package( Threads REQUIRED )

target_link_libraries( openssl_posix
                       PUBLIC
                          sockets_posix
                       PRIVATE
                          # This variable is set by the built-in FindOpenSSL.cmake
                          # and contains the path to the actual library.
                          ${OPENSSL_LIBRARIES}
                          # SSL uses Threads and on some platforms require
                          # explicit linking.
                          Threads::Threads
                          # SSL uses Dynamic Loading and on some platforms
                          # requires explicit linking.
                          ${CMAKE_DL_LIBS} )

if( BUILD_TESTS )
  add_subdirectory( utest )
endif()
