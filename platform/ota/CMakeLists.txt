add_library(ota_pal INTERFACE)
target_sources(ota_pal
    INTERFACE
    "src/pal/aws_ota_pal.c"
)
target_link_libraries( ota_pal
    INTERFACE OpenSSL::Crypto
)

add_library(ota_os INTERFACE)
target_sources(ota_os
    INTERFACE
    "src/os/ota_os_posix.c"
)
target_include_directories(ota_os INTERFACE "include")
target_link_libraries( ota_os
    INTERFACE Threads::Threads ${LIB_RT}
)
