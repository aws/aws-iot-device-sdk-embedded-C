# Check if the mbed TLS source directory exists.
if( NOT EXISTS ${PROJECT_SOURCE_DIR}/third_party/mbedtls/mbedtls/library/ )
    # Attempt to clone the mbed TLS submodule.
    if( ${IOT_BUILD_CLONE_SUBMODULES} )
        find_package( Git REQUIRED )

        message( "Cloning submodule mbed TLS." )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init third_party/mbedtls/mbedtls
                         WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                         RESULT_VARIABLE MBEDTLS_CLONE_RESULT )

        if( NOT ${MBEDTLS_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone mbed TLS submodule." )
        endif()
    else()
        message( FATAL_ERROR "The required submodule mbed TLS does not exist. Either clone it manually, or set IOT_BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endif()

# mbed TLS source files.
add_library( mbedtls
             mbedtls/library/ssl_tls.c )

# mbed TLS config header.
target_include_directories( mbedtls
                            PRIVATE ${PROJECT_SOURCE_DIR}/third_party/mbedtls )
target_compile_definitions( mbedtls
                            PRIVATE -DMBEDTLS_CONFIG_FILE="iot_config_mbedtls.h" )

# Disable all warnings for this third-party library.
target_compile_options( mbedtls
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w> )
