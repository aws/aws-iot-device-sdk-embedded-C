# Check if the TinyCBOR source directory exists.
if( NOT EXISTS ${PROJECT_SOURCE_DIR}/third_party/tinycbor/tinycbor/src/ )
    # Attempt to clone the TinyCBOR submodule.
    if( ${IOT_BUILD_CLONE_SUBMODULES} )
        find_package( Git REQUIRED )

        message( "Cloning submodule TinyCBOR." )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init third_party/tinycbor/tinycbor
                         WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                         RESULT_VARIABLE TINYCBOR_CLONE_RESULT )

        if( NOT ${TINYCBOR_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone TinyCBOR submodule." )
        endif()
    else()
        message( FATAL_ERROR "The required submodule TinyCBOR does not exist. Either clone it manually, or set IOT_BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endif()

# TinyCBOR library source files.
set( TINYCBOR_SOURCES
     tinycbor/src/cborencoder.c
     tinycbor/src/cborencoder_close_container_checked.c
     tinycbor/src/cborerrorstrings.c
     tinycbor/src/cborparser.c
     tinycbor/src/cborparser_dup_string.c
     tinycbor/src/cborpretty.c
     tinycbor/src/cborpretty_stdio.c )

# TinyCBOR headers (for folder organization only).
file( GLOB TINYCBOR_HEADERS "tinycbor/src/*.h" )

# TinyCBOR library target.
add_library( tinycbor
             ${TINYCBOR_SOURCES} ${TINYCBOR_HEADERS} )

# TinyCBOR include path.
target_include_directories( tinycbor SYSTEM
                            PUBLIC tinycbor/src )

# Disable all warnings for this third-party library.
target_compile_options( tinycbor
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w>
                        $<$<C_COMPILER_ID:MSVC>:
                        /W0 /D_CRT_SECURE_NO_WARNINGS> )

# Organization of TinyCBOR in folders.
set_property( TARGET tinycbor PROPERTY FOLDER third_party )
source_group( include FILES ${TINYCBOR_HEADERS} )
source_group( source FILES ${TINYCBOR_SOURCES} )
