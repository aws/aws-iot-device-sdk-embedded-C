# Add each subdirectory in the current directory with a CMakeLists.txt file in it
file(GLOB_RECURSE test_modules "${CMAKE_CURRENT_LIST_DIR}/*/CMakeLists.txt")
foreach(module IN LISTS test_modules)
    get_filename_component(DIR_PATH "${module}" DIRECTORY)
    add_subdirectory(${DIR_PATH})
endforeach()

# Filter demos based on what packages or library exist.
if(NOT ${OpenSSL_FOUND})
    set( openssl_tests
            "http_system_test"
            "mqtt_system_test"
            "shadow_system_test"
    )
    message( WARNING "OpenSSL library could not be found. Tests that use it will be excluded from the default target." )
    foreach(test_name ${openssl_tests})
        set_target_properties(${test_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endforeach()
endif()
