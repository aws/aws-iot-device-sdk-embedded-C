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
                          # This variable is set by the built-in FindOpenSSL.cmake
                          # and contains the path to the actual library.
                          ${OPENSSL_LIBRARIES}
                       PRIVATE
                          # SSL uses Threads and on some platforms require
                          # explicit linking.
                          Threads::Threads
                          # SSL uses Dynamic Loading and on some platforms
                          # requires explicit linking.
                          ${CMAKE_DL_LIBS} )

target_include_directories( openssl_posix
                            PUBLIC
                                ${OPENSSL_INCLUDE_DIR}
)

# Create target for POSIX implementation of MbedTLS transport
add_library( transport_mbedtls_posix
             ${MBEDTLS_TRANSPORT_SOURCES} )

target_link_libraries( transport_mbedtls_posix
                       PRIVATE
                           mbedtls )

target_include_directories(
    transport_mbedtls_posix
    PUBLIC
        ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
        ${LOGGING_INCLUDE_DIRS}
        ${TRANSPORT_INTERFACE_INCLUDE_DIR}
)

# Install transport implementations as both shared and static libraries.
if(INSTALL_PLATFORM_ABSTRACTIONS)
    install(TARGETS
      openssl_posix
      plaintext_posix
      sockets_posix
      transport_mbedtls_posix
      LIBRARY DESTINATION "${CSDK_LIB_INSTALL_PATH}"
      ARCHIVE DESTINATION "${CSDK_LIB_INSTALL_PATH}")
endif()
