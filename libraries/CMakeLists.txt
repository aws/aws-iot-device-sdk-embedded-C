# Add build configuration for all AWS modules.
file(GLOB aws_modules "${MODULES_DIR}/aws/*")
foreach(module IN LISTS aws_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

# Add build configuration for only JSON and HTTP modules. 
# Note: This is temporary and expected to be removed when
# submodules to coreHTTP and coreJSON repositories are added.
add_subdirectory( standard/http )
add_subdirectory( standard/json )

add_subdirectory(${3RDPARTY_DIR})
