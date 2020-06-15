# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Network library source files.
set( NETWORK_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/src/connect.c
     ${CMAKE_CURRENT_LIST_DIR}/src/plaintext_transport.c )

# Network library Public Include directories.
set( NETWORK_INCLUDE_PUBLIC_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/include )

# Network library Private Include directories.
set( NETWORK_INCLUDE_PRIVATE_DIRS
     ${PLATFORM_DIR}/include )
