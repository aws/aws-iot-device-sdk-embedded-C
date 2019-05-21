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
set( MBEDTLS_SOURCES
     mbedtls/library/aes.c
     mbedtls/library/aesni.c
     mbedtls/library/asn1parse.c
     mbedtls/library/asn1write.c
     mbedtls/library/base64.c
     mbedtls/library/bignum.c
     mbedtls/library/ecdh.c
     mbedtls/library/ecdsa.c
     mbedtls/library/ecp.c
     mbedtls/library/ecp_curves.c
     mbedtls/library/entropy.c
     mbedtls/library/entropy_poll.c
     mbedtls/library/error.c
     mbedtls/library/cipher.c
     mbedtls/library/cipher_wrap.c
     mbedtls/library/ctr_drbg.c
     mbedtls/library/hmac_drbg.c
     mbedtls/library/md.c
     mbedtls/library/md_wrap.c
     mbedtls/library/net_sockets.c
     mbedtls/library/oid.c
     mbedtls/library/pem.c
     mbedtls/library/pk.c
     mbedtls/library/pkparse.c
     mbedtls/library/pk_wrap.c
     mbedtls/library/platform.c
     mbedtls/library/platform_util.c
     mbedtls/library/rsa.c
     mbedtls/library/rsa_internal.c
     mbedtls/library/sha256.c
     mbedtls/library/sha512.c
     mbedtls/library/ssl_ciphersuites.c
     mbedtls/library/ssl_cli.c
     mbedtls/library/ssl_tls.c
     mbedtls/library/timing.c
     mbedtls/library/threading.c
     mbedtls/library/x509.c
     mbedtls/library/x509_crt.c )

# mbed TLS headers (for folder organization only).
file( GLOB MBEDTLS_HEADERS "mbedtls/include/mbedtls/*.h" )

# mbed TLS library target.
add_library( mbedtls
             ${MBEDTLS_SOURCES} ${MBEDTLS_HEADERS}
             iot_config_mbedtls.h threading_alt.h )

# mbed TLS config header and include directories.
target_include_directories( mbedtls SYSTEM
                            PUBLIC ${PROJECT_SOURCE_DIR}/third_party/mbedtls
                            PUBLIC ${PROJECT_SOURCE_DIR}/third_party/mbedtls/mbedtls/include )
target_compile_definitions( mbedtls
                            PUBLIC -DMBEDTLS_CONFIG_FILE="iot_config_mbedtls.h" )

# Link the Unity test framework when testing.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( mbedtls PRIVATE unity )
endif()

# Disable all warnings for this third-party library.
target_compile_options( mbedtls
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w>
                        $<$<C_COMPILER_ID:MSVC>:
                        /W0 /D_CRT_SECURE_NO_WARNINGS> )

# Organization of mbed TLS in folders.
set_property( TARGET mbedtls PROPERTY FOLDER "third_party" )
source_group( include\\mbedtls FILES ${MBEDTLS_HEADERS} )
source_group( source FILES ${MBEDTLS_SOURCES} )
source_group( "" FILES iot_config_mbedtls.h threading_alt.h iot_mbedtls_threading.c )
