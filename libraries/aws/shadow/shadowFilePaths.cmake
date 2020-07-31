# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# SHADOW library source files.
set( SHADOW_SOURCES
     ${MODULES_DIR}/aws/shadow/src/shadow.c )

# SHADOW library Public Include directories.
# Temporary adding utest into PUBLIC_DIRS to make shadow_config.h visible
# Will remove it after shadow demo is merged
set( SHADOW_INCLUDE_PUBLIC_DIRS
     ${MODULES_DIR}/aws/shadow/include
     ${MODULES_DIR}/aws/shadow/utest )
