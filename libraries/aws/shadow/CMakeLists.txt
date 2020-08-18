# Include filepaths for source and include.
include( shadowFilePaths.cmake )

# SHADOW library target.
add_library( shadow
             ${SHADOW_SOURCES} )

# SHADOW public include path.
target_include_directories( shadow PUBLIC ${SHADOW_INCLUDE_PUBLIC_DIRS}
                                          ${LOGGING_INCLUDE_DIRS} )

# SHADOW private include path.
target_include_directories( shadow PRIVATE ${SHADOW_INCLUDE_PRIVATE_DIRS}
                                           ${LOGGING_INCLUDE_DIRS} )

# Organization of SHADOW in IDE projects.
set_target_properties( shadow  PROPERTIES FOLDER libraries/aws )
source_group( include FILES include/shadow.h)
source_group( src FILES ${SHADOW_SOURCES} )

if(BUILD_TESTS)
    add_subdirectory( utest )
    add_subdirectory( integration-test )
endif()
