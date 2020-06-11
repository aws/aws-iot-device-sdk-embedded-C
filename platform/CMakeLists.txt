# Include filepaths for source and include.
include( platformFilePaths.cmake )

# PLATFORM library target.
add_library( platform
             ${PLATFORM_SOURCES} )

# PLATFORM public include path.
target_include_directories( platform PUBLIC ${PLATFORM_INCLUDE_PUBLIC_DIRS} )

source_group( src FILES ${PLATFORM_SOURCES} )

# Add all CMakeLists.txts in the subfolders.
# file(GLOB platform_modules "${PLATFORM_DIR}/*")
# foreach(module IN LISTS platform_modules )
#    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
#        add_subdirectory(${module})
#    endif()
# endforeach()