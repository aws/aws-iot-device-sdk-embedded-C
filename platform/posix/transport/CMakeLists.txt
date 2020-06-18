# Include filepaths for source and include.
include(transportFilePaths.cmake)

# Create target for POSIX implementation of TCP.
add_library( tcp_posix
             ${TCP_TRANSPORT_SOURCES} )

target_include_directories( tcp_posix PUBLIC ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
                                             ${LOGGING_INCLUDE_DIRS} )

target_include_directories( tcp_posix PRIVATE ${COMMON_TRANSPORT_INCLUDE_PRIVATE_DIRS} )

# Create target for POSIX implementation of OpenSSL.
add_library( openssl_posix
             ${OPENSSL_TRANSPORT_SOURCES} )

target_include_directories( openssl_posix PUBLIC ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
                                                 ${LOGGING_INCLUDE_DIRS} )

target_include_directories( openssl_posix PRIVATE ${COMMON_TRANSPORT_INCLUDE_PRIVATE_DIRS} )
