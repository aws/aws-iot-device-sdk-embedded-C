# CMake library target for tls_utils.
set(OPENSSL_USE_STATIC_LIBS TRUE)
find_package(OpenSSL REQUIRED)

set( CMAKE_THREAD_PREFER_PTHREAD ON )
find_package(Threads REQUIRED)

add_library( tls_utils tls_utils.c )

target_link_libraries(
    tls_utils
    PRIVATE
        OpenSSL::Crypto
        OpenSSL::SSL
	# SSL uses Threads and on some platforms require explicit linking.
        Threads::Threads
	# SSL uses Dynamic Loading and on some platforms requires explicit linking.
        ${CMAKE_DL_LIBS}
    # Dependency on mqtt for MQTTNetworkContext_t type.
        mqtt
)

target_include_directories(
    tls_utils
    PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
)