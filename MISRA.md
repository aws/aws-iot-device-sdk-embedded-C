# MISRA Compliance

The POSIX platform implementations of transport interfaces, clock utility and retry utils conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Deviations from the MISRA standard are listed below:

### Ignored by [Coverity Configuration](tools/coverity/misra.config)
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.5 | Advisory | Allow names that MISRA considers ambiguous (such as LogInfo and LogError) |
| Directive 4.8 | Advisory | Allow inclusion of unused types. Header files for a specific port, which are needed by all files, may define types that are not used by a specific file. |
| Directive 4.9 | Advisory | Allow inclusion of function like macros. The `assert` macro is used throughout the library for parameter validation, and logging is done using function like macros. |
| Rule 2.3 | Advisory | Allow unused types. Library headers may define types intended for the application's use, but not used within the library files. |
| Rule 2.4 | Advisory | Allow unused tags. Some compilers warn if types are not tagged. |
| Rule 2.5 | Advisory | Allow unused macros. Library headers may define macros intended for the application's use, but are not used by a specific file. |
| Rule 3.1 | Required | Allow nested comments. C++ style `//` comments are used in example code within Doxygen documentation blocks. |
| Rule 11.5 | Advisory | Allow casts from `void *`. Fields may be passed as `void *`, requiring a cast to the correct data type before use. |
| Rule 21.1 | Required | Allow use of all macro names. For compatibility, libraries may define macros introduced in C99 for use with C90 compilers. |
| Rule 21.2 | Required | Allow use of all macro and identifier names. For compatibility, libraries may define macros introduced in C99 for use with C90 compilers. |

### Flagged by Coverity
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Rule 5.6 | Required | The header file `transport_interface.h` is present in each library repository that depends on the transport interface. This is to be able to independently compile the library repository build targets. When all the targets are analyzed together, Coverity flags the type duplication caused by multiple copies of header files in this repository as violations. However, this violation will not be flagged if each library repository build target is analyzed individually. |
| Rule 5.7 | Required | The network context struct is defined by each transport implementation; however, only one transport implementation is needed by an application at a time. If the transport implementations are analyzed one at a time by Coverity, this violation will not be flagged. |
| Rule 8.7 | Advisory | API functions are not used by the library outside of the files they are defined; however, they must be externally visible in order to be used by an application. |
| Rule 8.13 | Advisory | The object pointed to by `pNetworkContext` is not modified by POSIX sockets or OpenSSL, but other implementations of `TransportRecv_t` and `TransportSend_t` may do so. |

### Suppressed with Coverity Comments
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.6 | Advisory | Basic numerical types are used in platform implementations, since the POSIX platform functions and OpenSSL functions used in the platform implementations take arguments of these types. |
| Rule 10.1 | Required | A POSIX-specific macro utility `FD_SET` is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 10.8 | Required | A POSIX-specific macro utility `FD_SET` is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 11.3 | Required | The transport implementation casts an object pointer to a pointer of a different object type. This cast is supported in POSIX, and is used to obtain IP addresses from address records. |
| Rule 11.8 | Required | An OpenSSL API `SSL_set_tlsext_host_name`, which is used in the TLS transport implementation, internally casts a string literal to a `void *` pointer. |
| Rule 13.4 | Required | A POSIX-specific macro utility `FD_SET` is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 14.4 | Required | A POSIX-specific macro utility `FD_ZERO` is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 21.6 | Required | The Standard Library input/output functions for opening and closing files are used by the OpenSSL transport implementation, since the OpenSSL API `PEM_read_X509` to read PEM files takes `FILE *` as an argument. The standard C library file handling functions are also used in POSIX platform implementation of OTA. |
