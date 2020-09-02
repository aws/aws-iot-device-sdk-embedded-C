# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Sockets utility source files.
set( SOCKETS_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/sockets_posix.c )

# Plaintext transport source files.
set( PLAINTEXT_TRANSPORT_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/plaintext_posix.c )

# OpenSSL transport source files.
set( OPENSSL_TRANSPORT_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/openssl_posix.c )

# Reconnect logic source files.
set( RECONNECT_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/transport_reconnect_posix.c )

# Transport Public Include directories.
set( COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/include
     ${PLATFORM_DIR}/include )
