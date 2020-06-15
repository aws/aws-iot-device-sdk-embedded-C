# Include filepaths for source and include.
include(networkFilePaths.cmake)

# network library target.
add_library( network
             ${NETWORK_SOURCES} )

# network public include path.
target_include_directories( network PUBLIC ${NETWORK_INCLUDE_PUBLIC_DIRS}
                                           ${LOGGING_INCLUDE_DIRS} )

# network private include path.
target_include_directories( network PUBLIC ${NETWORK_INCLUDE_PRIVATE_DIRS} )
