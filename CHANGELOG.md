## 0.4.0 (October 5, 2015)

Features:

  - Thing Shadow Actions - Update, Delete, Get for any Thing Name
  - aws_iot_config.h file for easy configuration of parameters
  - Sample app for talking with console's Interactive guide
  - disconnect handler for the MQTT client library
  
Bugfixes/Improvements:

  - mbedTLS read times out every 10 ms instead of hanging for ever
  - mbedTLS handshake failure handled

## 0.3.0 (September 14, 2015)

Features:

  - Testing with mbedTLS, prepping for relase

Bugfixes/Improvements:

  - Refactored to break out timer and network interfaces

## 0.2.0 (September 2, 2015)

Features:

  - Added initial Shadow implementation + example
  - Added hostname verification to OpenSSL example
  - Added iot_log interface
  - Initial API Docs (Doxygen)

Bugfixes/Improvements:

  - Fixed yield timeout
  - Refactored APIs to pass by reference vs value

## 0.1.0 (August 12, 2015)

Features:

  - Initial beta release
  - MQTT Publish and Subscribe
  - TLS mutual auth on linux with OpenSSL

Bugfixes/Improvements:
	- N/A
