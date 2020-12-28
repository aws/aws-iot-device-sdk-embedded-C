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

# Install transport implementations as libraries.
if(INSTALL_PLATFORM_ABSTRACTIONS)
    install(TARGETS
      openssl_posix
      plaintext_posix
      sockets_posix
      LIBRARY DESTINATION "${CSDK_LIB_INSTALL_PATH}")
endif()

if( BUILD_TESTS )
  add_subdirectory( utest )
endif()
