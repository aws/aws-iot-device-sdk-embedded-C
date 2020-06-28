# Include filepaths for source and include.
include(transportFilePaths.cmake)

# Create target for sockets utility.
add_library( sockets_posix
                ${SOCKETS_SOURCES} )

target_include_directories( sockets_posix 
                              PUBLIC 
                                ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
                                ${LOGGING_INCLUDE_DIRS} )

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
                           sockets_posix )

# Create target for POSIX implementation of reconnect logic.
add_library( reconnect_posix 
               ${RECONNECT_SOURCES} )

target_include_directories( reconnect_posix 
                              PUBLIC 
                                ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
                                ${LOGGING_INCLUDE_DIRS} )