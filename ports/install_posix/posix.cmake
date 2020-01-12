# Install binaries according GNU coding standards
function( InstallBinary TARGET)
    include( GNUInstallDirs )
    install( TARGETS ${TARGET}
             RUNTIME
             DESTINATION ${CMAKE_INSTALL_FULL_BINDIR}
             LIBRARY
             DESTINATION ${CMAKE_INSTALL_FULL_LIBDIR}
             ARCHIVE
             DESTINATION ${CMAKE_INSTALL_FULL_LIBDIR} )
endfunction()

# Install headers according GNU coding standards
function( InstallHeaders HEADERS PREFIX)
    include( GNUInstallDirs )
    list( LENGTH ${HEADERS} LIST_LEN )
    if( LIST_LEN )
        set( LOCAL_HEADERS ${${HEADERS}} )
    else()
        set( LOCAL_HEADERS ${HEADERS} )
    endif()
    install( FILES ${LOCAL_HEADERS}
            DESTINATION ${CMAKE_INSTALL_FULL_INCLUDEDIR}/${PREFIX} )
endfunction()

# Prepare RPATH
function( PrepareRPATH )
    include( GNUInstallDirs )

    # the RPATH to be used when installing, but only if it's not a system directory
    list( FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_FULL_LIBDIR}" isSystemDir )
    if( "${isSystemDir}" STREQUAL "-1" )
        set( CMAKE_INSTALL_RPATH ${CMAKE_INSTALL_FULL_LIBDIR} PARENT_SCOPE)
        set( CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE PARENT_SCOPE)
    endif()
endfunction()