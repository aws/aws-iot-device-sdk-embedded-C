# Changelog for AWS IoT Device SDK for Embedded C

## 202211.00 (November 2022)

### Major Changes
 - This release includes an update to how the [Coverity static analysis](https://scan.coverity.com/) scans are performed. There is now a **tools/coverity/README.md** file in each library with instructions on how to perform a scan with 0 [MISRA coding standard](https://www.misra.org.uk) warnings or errors.
- [#1823](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1823) Update library submodule pointers to use the same versions used in **[FreeRTOS LTS 202210.01-LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/blob/202210-LTS/CHANGELOG.md)**. The versions of the libraries used for this release went through extensive testing as described in the **[LTS Code Quality Checklist](https://www.freertos.org/lts-libraries.html)**. Further information about the changes can be found in the CHANGELOG.md file in each library.
- [#1779](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1779) Update version of MbedTLS from v2.26.0 to v2.28.0

### Minor Changes
- [#1831](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1831) Create a demo for connecting a device to a [Greengrass](https://docs.aws.amazon.com/greengrass/v2/developerguide/getting-started.html) core using the [new feature](https://docs.aws.amazon.com/greengrass/v2/developerguide/greengrass-release-2022-11-15.html) that allows using custom CAs.
- [#1826](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1826) Adds a test to verify multiple subscription and unsubscribe requests succeed when done through a single API call.
- [#1809](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1809) Reduce the likelihood of encountering transient connection issues by setting TRANSPORT_SEND_RECV_TIMEOUT_MS to a minimum of 1000ms in all tests and demos.

## 202108.00 (August 2021)

### Major Changes
- This release introduces the refactored **[AWS IoT Fleet Provisioning](https://github.com/aws/fleet-provisioning-for-aws-iot-embedded-sdk)** library and **[AWS SigV4](https://github.com/aws/SigV4-for-AWS-IoT-embedded-sdk)** library.
These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score greater than 8, checks against deviations from the mandatory rules in the [MISRA coding standard](https://www.misra.org.uk), static code analysis from [Coverity static analysis](https://scan.coverity.com/) and validation of memory safety through the [CBMC automated reasoning tool](http://www.cs.cmu.edu/~modelcheck/cbmc/).
- [#1692](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1692) Update the existing HTTP S3 download demo to obtain temporary credentials from [AWS IoT Credential Provider](https://docs.aws.amazon.com/iot/latest/developerguide/authorizing-direct-aws.html) and use the the new **AWS SigV4 library**  to sign HTTP requests with those credentials for authenticating with AWS S3 service.
- [#1688](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1688) Add Demo to showcase use of **AWS IoT Fleet Provisioning** library using the ["Provisioning by Claim"](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#claim-based) workflow of the Fleet Provisioning feature of AWS IoT Core.
- [#1680](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1680) Add new transport interface implementation using **Mbed TLS** (for TLS stack) and **corePKCS11** (for credential management).

### Minor Changes

- [#1670](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1670) Update corePKCS11 demo to read the public key as the private key was being used to both sign and verify
- [#1596](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1596) Make `THING_NAME` an alias for `CLIENT_IDENTIFIER` in MQTT-related demos
- [#1593](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1593) Initialize MQTT status return code in OTA demos mqtt_publish
- [#1599](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1599) Checking execution status of demo loop before calling pthread_join in OTA demos

## 202103.00 (March 2021)

### Major Changes

- Changes brought through submodule update of libraries:
  - [AWS IoT Over-the-air Update library v3.0.0](https://github.com/aws/ota-for-aws-iot-embedded-sdk/tree/v3.0.0) is now generally available.
  - Updated [AWS IoT Device Shadow library](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/tree/v1.1.0) to support named shadow, a feature of the AWS IoT Device Shadow service that allows you to create multiple shadows for a single IoT device.
  - Updated [AWS IoT Device Defender library](https://github.com/aws/device-defender-for-aws-iot-embedded-sdk/tree/v1.1.0) to support custom metrics, a feature that helps you monitor operational health metrics that are unique to your fleet or use case.
- Changes brought through pushing commits to AWS IoT Device SDK for Embedded C:
  - [#1547](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1547) Update the Device Defender demo to showcase reporting of custom metrics to the AWS IoT Device Defender service.
  - AWS IoT Over-the-air Update library v3.0.0 is now generally available.
  - [#1529](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1529), [#1532](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1532) Update Jobs demo to use DescribeJobExecution API instead of StartNextPendingJobExecution API, and disable functionality of periodic job updates by default.
  - [#1519](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1519) Add an `install` target for installing libraries and headers in file system.

### Minor Changes

 - [#1511](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1511) Fix memory leak in PKCS #11 test.
 - [#1539](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1539) Add retries for MQTT publishing with the backoffAlgorithm library.
 - [#1516](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1516), [#1538](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1538), [#1540](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1540), [#1487](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1487) Minor bugfixes and refactoring of the OTA demos and OTA PAL for POSIX.
 - [#1552](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1552) Update broken links in demo comments and documentation.
 - [# #1599](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1599) In OTA demo add check before calling pthread_join.

## 202012.01 (December 2020)

### Major Changes

- This release introduces the **AWS IoT Over-the-air Update** library(Release Candidate), **backoffAlgorithm** library, and **PKCS #11** library.
These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score greater than 8, checks against deviations from the mandatory rules in the [MISRA coding standard](https://www.misra.org.uk), and static code analysis from [Coverity statical analysis](https://scan.coverity.com/). In addition, PKCS11 library has also undergone validation of memory safety through the [CBMC automated reasoning tool](http://www.cs.cmu.edu/~modelcheck/cbmc/).

- This release uses submodule references to the following new individual repositories for the AWS IoT Over-the-air Update, backoffAlgorithm, and PKCS11 libraries under the `libraries` folder:
   - [aws/ota-for-aws-iot-embedded-sdk](https://github.com/aws/ota-for-aws-iot-embedded-sdk) for the AWS IoT Over-the-air Update library.
   - [FreeRTOS/backoffAlgorithm](https://github.com/FreeRTOS/backoffAlgorithm) for the backoffAlgorithm library.
   - [FreeRTOS/corePKCS11](https://github.com/FreeRTOS/corePKCS11) for the PKCS11 library.

## 202011.00 (November 2020)

### Major Changes

- This release introduces the re-factored **HTTP** client library, **AWS IoT Device Defender** client library, and **AWS IoT Jobs** client library.
These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score greater than 8, and checks against deviations from the mandatory rules in the [MISRA coding standard](https://www.misra.org.uk). These libraries have also undergone both static code analysis from [Coverity statical analysis](https://scan.coverity.com/) and validation of memory safety through the [CBMC automated reasoning tool](http://www.cs.cmu.edu/~modelcheck/cbmc/).

- This release uses submodule references to the following new individual repositories for the HTTP, AWS IoT Device Defender client, and AWS IoT Jobs client libraries under the `libraries` folder:
   - [FreeRTOS/coreHTTP](https://github.com/FreeRTOS/coreHTTP) for the HTTP client library
   - [aws/device-defender-for-aws-iot-embedded-sdk](https://github.com/aws/device-defender-for-aws-iot-embedded-sdk) for the AWS IoT Device Defender client library.
   - [aws/jobs-for-aws-iot-embedded-sdk](https://github.com/aws/jobs-for-aws-iot-embedded-sdk) for the AWS IoT Jobs client library.

## 202009.00 (September 2020)

### Major Changes

- This release introduces the re-factored **MQTT** client library, **JSON** parser library, and **AWS IoT Device Shadow** client library.
These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score greater than 8, and checks against deviations from the mandatory rules in the [MISRA coding standard](https://www.misra.org.uk). These libraries have also undergone both static code analysis from [Coverity statical analysis](https://scan.coverity.com/) and validation of memory safety through the [CBMC automated reasoning tool](http://www.cs.cmu.edu/~modelcheck/cbmc/).

- This release uses submodule references to the following new individual repositories for the MQTT, JSON, and AWS IoT Device Shadow client libraries under the `libraries` folder:
   - [FreeRTOS/coreMQTT](https://github.com/FreeRTOS/coreMQTT) for the MQTT client library
   - [FreeRTOS/coreJSON](https://github.com/FreeRTOS/coreJSON) for the JSON parser library
   - [aws/device-shadow-for-aws-iot-embedded-sdk](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk) for the AWS IoT Device Shadow client library.

- With this release, we are introducing a [date-based versioning scheme](README.md#versioning).

**Note**: This release is **NOT** backwards compatible with the v3 version of AWS IoT Device SDK for Embedded C.

## [3.1.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v3.1.0) (September 08, 2020)

This represents the last tag for the v3 version of AWS IoT Device SDK for Embedded C.

Bugfixes:
- [#205](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/205) Fix IAR compiler error about missing function prototypes.
- [#241](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/241) Fix command-line argument processing in Shadow demo.
- [#244](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/244) Fix parsing of metadata object in delta callback.
- [#854](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/854) Fix doxygen errors in v3 MQTT documentation.
- [#895](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/895) Fix issues reported by clang static analysis.
- [#1006](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1006) Fix application hang when network is lost during QoS0 publish loop.
- [#1070](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/1070) Fix typo in job's status strings.

## [3.0.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v3.0.1) (May 10, 2018)

Bugfixes:

  - [#167](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/167), [#168](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/168) Fixed issues reported by Coverity Scan.
  - [#177](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/177) Fixes a memory corruption bug and handling of timeouts.

Other:

  - Add .travis.yml for Travis CI.
  - Removed C++ sample.
  - Removed includes of `inttypes.h`, which doesn't exist on some systems.
  - [#175](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/175) Added comments on static allocation of MQTT topics.

## [3.0.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v3.0.0) (Apr 17, 2018)

Bugfixes:

  - [#152](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/152) Fixes potential buffer overflows in `parseStringValue` by requiring a size parameter in `jsonStruct_t`.
  - [#155](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/155) Fixes other memory corruption bugs; also improves stability.

The two bug fixes above are not backwards compatible with v2.3.0.  Please see [README.md](README.md#migrating-from-2x-to-3x) for details on migrating to v3.0.0.

## [2.3.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.3.0) (Mar 21, 2018)

New Features:

  - Add [AWS IoT Jobs](https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html) support.
  - Use AWS IoT Core support for MQTT over port 443. MQTT connection now defaults to port 443.

Pull requests:

  - [#124](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/124) - Thing Shadow: Fix potential shadow buffer overflow
  - [#135](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/135) - mbedtls_wrap: Fix unintialized variable usage
  - Fix bugs in long-running integration tests.

## [2.2.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.2.1) (Dec 26, 2017)

Bugfixes:

  - [#115](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/115) - Issue with new client metrics

Pull requests:

  - [#112](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/112) - Initialize msqParams.isRetained to 0 in publishToShadowAction()
  - [#118](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/118) - mqttInitParams.mqttPacketTimeout_ms initialized

## [2.2.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.2.0) (Nov 22, 2017)

New Features:

  - Added SDK metrics string into connect packet

Bugfixes:

  - [#49](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/49) - Add support for SHADOW_JSON_STRING as supported value
  - [#57](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/57) - remove unistd.h
  - [#58](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/58) - Fix return type of aws_iot_mqtt_internal_is_topic_matched
  - [#59](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/95) - Fix extraneous assignment
  - [#62](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/62) - Clearing SubscriptionList entries in shadowActionAcks after subscription failure
  - [#63](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/63) - Stack overflow when IOT_DEBUG is enabled
  - [#66](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/66) - Bug in send packet function
  - [#69](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/69) - Fix for broken deleteActionHandler in shadow API
  - [#71](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/71) - Prevent messages on /update/accepted from incrementing shadowJsonVersionNum in delta
  - [#73](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/73) - wait for all messages to be received in subscribe publish sample
  - [#96](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/96) - destroy TLS instance even if disconnect send fails
  - Fix for aws_iot_mqtt_resubscribe not properly resubscribing to all topics
  - Update MbedTLS Network layer Readme to remove specific version link
  - Fix for not Passing througheError code on aws_iot_shadow_connect failure
  - Allow sending of SHADOW_JSON_OBJECT to the shadow
  - Ignore delta token callback for metadata
  - Fix infinite publish exiting early in subscribe publish sample

Improvements:

  - Updated jsmn to latest commit
  - Change default keepalive interval to 600 seconds

Pull requests:

  - [#29](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/29) - three small fixes
  - [#59](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/59) - Fixed MQTT header constructing and parsing
  - [#88](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/88) - Fix username and password are confused
  - [#78](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/78) - Fixed compilation warnings
  - [#102](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/102) - Corrected markdown headers
  - [#105](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/105) - Fixed warnings when compiling

## [2.1.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.1.1) (Sep 5, 2016)

Bugfixes/Improvements:

  - Network layer interface improvements to address reported issues
  - Incorporated GitHub pull request [#41](https://github.com/aws/aws-iot-device-sdk-embedded-c/pull/41)
  - Bugfixes for issues [#36](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/36) and [#33](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/33)

## [2.1.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.1.0) (Jun 15, 2016)

New features:

  - Added unit tests, further details can be found in the testing [readme](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/v2.1.0/tests/README.md/)
  - Added sample to demonstrate building the SDK as library
  - Added sample to demonstrate building the SDK in C++

Bugfixes/Improvements:

  - Increased default value of Maximum Reconnect Wait interval to 128 secs
  - Increased default value of MQTT Command Timeout in Shadow Connect to 20 secs
  - Shadow null/length checks
  - Client Id Length not passed correctly in shadow connect
  - Add extern C to headers and source files, added sample to demonstrate usage with C++
  - Delete/Accepted not being reported, callback added for delete/accepted
  - Append IOT_ to all Debug macros (eg. DEBUG is now IOT_DEBUG)
  - Fixed exit on error for subscribe_publish_sample

## [2.0.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v2.0.0) (April 28, 2016)

New features:

  - Refactored API to make it instance specific. This is a breaking change in the API from 1.x releases because a Client Instance parameter had to be added to all APIs
  - Added Threading library porting layer wrapper
  - Added support for multiple connections from one application
  - Shadows and connections de-linked, connection needs to be set up separately, can be used independently of shadow
  - Added integration tests for testing SDK functionality

Bugfixes/Improvements:

  - Yield cannot be called again while waiting for application callback to return
  - Fixed issue with TLS layer handles not being cleaned up properly on connection failure reported [here](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/16)
  - Renamed timer_linux.h to timer_platform.h as requested [here](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/5)
  - Adds support for disconnect handler to shadow. A similar pull request can be found [here](https://github.com/aws/aws-iot-device-sdk-embedded-C/pull/9)
  - New SDK folder structure, cleaned and simplified code structure
  - Removed Paho Wrapper, Merge MQTT into SDK code, added specific error codes
  - Refactored Network and Timer layer wrappers, added specific error codes
  - Refactored samples and makefiles

## [1.1.2](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v1.1.2) (April 22,  2016)

Bugfixes/Improvements:

  - Signature mismatch in MQTT library file fixed
  - Makefiles have a protective target on the top to prevent accidental execution

## [1.1.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v1.1.1) (April 1, 2016)

Bugfixes/Improvements:

  - Removing the Executable bit from all the files in the repository. Fixing [this](https://github.com/aws/aws-iot-device-sdk-embedded-C/issues/14) issue
  - Refactoring MQTT client to remove declaration after statement warnings
  - Fixing [this](https://forums.aws.amazon.com/thread.jspa?threadID=222467&tstart=0) bug


## [1.1.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v1.1.0) (February 10, 2016)
Features:

  - Auto Reconnect and Resubscribe

Bugfixes/Improvements:

  - MQTT buffer handling incase of bigger message
  - Large timeout values converted to seconds and milliseconds
  - Dynamic loading of Shadow parameters. Client ID and Thing Name are not hard-coded
  - MQTT Library refactored


## [1.0.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v1.0.1) (October 21, 2015)

Bugfixes/Improvements:

  - Paho name changed to Eclipse Paho
  - Renamed the Makefiles in the samples directory
  - Device Shadow - Delete functionality macro fixed
  - `subscribe_publish_sample` updated

## [1.0.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/v1.0.0) (October 8, 2015)

Features:

  - Release to github
  - SDK tarballs made available for public download

Bugfixes/Improvements:
  - Updated API documentation

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
