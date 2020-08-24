# Configuration for CMock if testing is enabled.
if( ${BUILD_TESTS} )
    
    # Include the 3rdparty CMakeLists.txt for CMock build configuration.
    add_subdirectory(${3RDPARTY_DIR})

    # Create a list for each unit test target
    set(utest_targets 
            http_utest mqtt_utest 
            mqtt_lightweight_utest mqtt_state_utest 
            http_send_utest sockets_utest)

    # Add a target for running coverage on tests.
    add_custom_target(coverage
        COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
        DEPENDS cmock unity ${utest_targets}
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()

# Add all modules.
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
file(GLOB aws_modules "${MODULES_DIR}/aws/*")
foreach(module IN LISTS standard_modules aws_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

