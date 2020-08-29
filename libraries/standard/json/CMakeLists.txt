# Include filepaths for source and include.
include(jsonFilePaths.cmake)

# JSON library target.
add_library( json
             ${JSON_SOURCES} )

# JSON public include path.
target_include_directories( json PUBLIC ${JSON_INCLUDE_PUBLIC_DIRS}
                                        ${LOGGING_INCLUDE_DIRS} )

# Organization of JSON in IDE projects.
set_target_properties( json PROPERTIES FOLDER libraries/standard )
source_group( include FILES include/json.h )
source_group( src FILES ${JSON_SOURCES} )

if(BUILD_TESTS)
    add_subdirectory(utest)
endif()
