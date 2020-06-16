# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Demo library source files.
set( DEMO_SOURCES
     ${PLATFORM_DIR}/posix/network/src/network_utilities.c
     ${PLATFORM_DIR}/posix/network/src/plaintext_transport.c )

# Demo library Private Include directories.
set( DEMO_INCLUDE_PRIVATE_DIRS
     ${PLATFORM_DIR}/posix/network/include )
