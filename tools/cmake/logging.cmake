# Configuration for logging.
set( LOGGING_INCLUDE_DIRS
     ${ROOT_DIR}/platform/include )

set( LOGGING_SOURCES
     ${ROOT_DIR}/platform/posix/logging.c
     ${ROOT_DIR}/platform/posix/clock_posix.c )