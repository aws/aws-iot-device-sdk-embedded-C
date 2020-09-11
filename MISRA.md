# MISRA Compliance

The POSIX platform implementations of transport interfaces, clock utility and retry utils conform to the [MISRA C:2012](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Deviations from the MISRA standard are listed below:

### Ignored by [Coverity Configuration](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/master/tools/coverity/misra.config)
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.5 | Advisory | Allow names that MISRA considers ambiguous (such as LogInfo and LogError) |
| Directive 4.8 | Advisory | Allow inclusion of unused types. Header files for a specific port, which are needed by all files, may define types that are not used by a specific file. |
| Directive 4.9 | Advisory | Allow inclusion of function like macros. The `assert` macro is used throughout the library for parameter validation, and logging is done using function like macros. |
| Rule 2.3 | Advisory | Allow unused types. The `MQTTSubAckStatus_t` enum is unused in our source files, as it is intended for a user to use when parsing a subscription acknowledgment's response codes. |
| Rule 2.4 | Advisory | Allow unused tags. Some compilers warn if types are not tagged. |
| Rule 2.5 | Advisory | Allow unused macros. Library headers may define macros intended for the application's use, but are not used by a specific file. |
| Rule 3.1 | Required | Allow nested comments. C++ style `//` comments are used in example code within Doxygen documentation blocks. |
| Rule 11.5 | Advisory | Allow casts from `void *`. Fields such as publish payloads are passed as `void *` and must be cast to the correct data type before use. |
| Rule 21.1 | Required | Allow use of all macro names. For compatibility, some macros introduced in C99 are defined for use with C90 compilers. |
| Rule 21.2 | Required | Allow use of all macro and identifier names. For compatibility, some macros introduced in C99 are defined for use with C90 compilers. |

### Flagged by Coverity
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Rule 5.7 | Required | Type for network context is defined by each transport implementation; however only one transport implementation is needed by an application at a time. If the transport implementations are analyzed one at a time by Coverity, this violation will not be flagged. |
| Rule 8.7 | Advisory | API functions are not used by the library outside of the files they are defined; however, they must be externally visible in order to be used by an application. |

### Suppressed with Coverity Comments
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.6 | Advisory | Basic numerical types are used in platform implementations, since POSIX platform functions and openssl functions used in the platform implementations take arguments of basic numerical types. |
| Rule 10.1 | Required | POSIX specific macro utility is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 10.8 | Required | POSIX specific macro utility is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 11.3 | Required | Transport implementation casts a pointer of a object type to a pointer of a different object type. This casting is supported in POSIX and is used to obtain the IP address from a address record. |
| Rule 11.8 | Required | An openssl API used in TLS transport implementation internally casts the pointer to a string literal to a `void *` pointer. |
| Rule 13.4 | Required | POSIX specific macro utility is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 14.4 | Required | POSIX specific macro utility is flagged for this violation. This macro utility, whose implementation is supplied by the system, is used in the transport implementation. |
| Rule 21.6 | Required | The Standard Library input/output functions for opening and closing a file are used by the openssl transport implementation, as the openssl API to read a PEM file takes `FILE *` as an argument. |
