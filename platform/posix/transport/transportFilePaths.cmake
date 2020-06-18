# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Network library source files.
set( TCP_TRANSPORT_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/tcp_transport.c )

# Network library source files.
set( OPENSSL_TRANSPORT_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/openssl_transport.c )

# Transport Private Include directories.
set( COMMON_TRANSPORT_INCLUDE_PRIVATE_DIRS
     ${PLATFORM_DIR}/include )

# Transport Public Include directories.
set( COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/include )
