set(OPENSSL_USE_STATIC_LIBS TRUE)
find_package(OpenSSL REQUIRED)

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)

find_library(LIB_RT rt REQUIRED)

# Add the posix targets
add_subdirectory( ${PLATFORM_DIR}/posix )

# Add ota porting targets
# add_subdirectory( ${PLATFORM_DIR}/posix/ota_pal )
