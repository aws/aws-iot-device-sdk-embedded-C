# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.

# PLATFORM library source files.
set( PLATFORM_SOURCES
     "${PLATFORM_DIR}/posix/src/reconnect_posix.c" )

# PLATFORM library Public Include directories.
set( PLATFORM_INCLUDE_PUBLIC_DIRS
     "${PLATFORM_DIR}/include"
     "${PLATFORM_DIR}/*/include" )