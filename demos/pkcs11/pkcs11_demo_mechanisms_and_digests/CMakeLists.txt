set( DEMO_NAME "pkcs11_demo_mechanisms_and_digests" )

# Set path to corePKCS11 and its third party libraries.
set(COREPKCS11_LOCATION "${CMAKE_SOURCE_DIR}/libraries/standard/corePKCS11")
set(CORE_PKCS11_3RDPARTY_LOCATION "${COREPKCS11_LOCATION}/source/dependency/3rdparty")

# Include PKCS #11 library's source and header path variables.
include( ${COREPKCS11_LOCATION}/pkcsFilePaths.cmake )

list(APPEND PKCS_SOURCES
            "${DEMOS_DIR}/pkcs11/common/src/demo_helpers.c"
            "${COREPKCS11_LOCATION}/source/portable/posix/core_pkcs11_pal.c"
            "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils/mbedtls_utils.c"
            )

# Demo target.
add_executable(
    ${DEMO_NAME}
    "${DEMO_NAME}.c"
    ${PKCS_SOURCES}
)

target_link_libraries(
    ${DEMO_NAME}
    PRIVATE
        mbedtls
)

target_include_directories(
    ${DEMO_NAME}
    PUBLIC
        "${DEMOS_DIR}/pkcs11/common/include"
        ${PKCS_INCLUDE_PUBLIC_DIRS}
        ${CMAKE_CURRENT_LIST_DIR}
        ${LOGGING_INCLUDE_DIRS}
        "${CORE_PKCS11_3RDPARTY_LOCATION}/pkcs11"
    PRIVATE
        "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils"
)
