add_library(ota_pal INTERFACE)
target_sources(ota_pal
    INTERFACE
    "${CMAKE_CURRENT_SOURCE_DIR}/src/pal/aws_ota_pal.c"
)
target_link_libraries( ota_pal
    INTERFACE OpenSSL::Crypto
)
