add_library(ota_pal INTERFACE)
target_sources(ota_pal
    INTERFACE
    "${CMAKE_CURRENT_SOURCE_DIR}/source/ota_pal_posix.c"
)

target_include_directories( ota_pal
    INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/source/include
        ${LOGGING_INCLUDE_DIRS}
)

target_link_libraries( ota_pal
    INTERFACE ${OPENSSL_CRYPTO_LIBRARY}
)

if(${BUILD_TESTS})
  add_subdirectory(utest)
endif()
