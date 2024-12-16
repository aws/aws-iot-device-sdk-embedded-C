/*
 * AWS IoT Device SDK for Embedded C 202412.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#ifndef PKCS11_OPERATIONS_H_
#define PKCS11_OPERATIONS_H_

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>

/**
 * @brief To access the private members of the MbedTLS structs
 */
#define MBEDTLS_ALLOW_PRIVATE_ACCESS

/* corePKCS11 include. */
#include "core_pkcs11.h"

/**
 * @brief Loads the claim credentials into the PKCS #11 module. Claim
 * credentials are used in "Provisioning by Claim" workflow of Fleet
 * Provisioning feature of AWS IoT Core. For more information, refer to the
 * [AWS documentation](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#claim-based)
 *
 * Note: This function is for demonstration purposes, and the claim credentials
 * should be securely stored in production devices. For example, the
 * shared claim credentials could be loaded into a secure element on the devices
 * in your fleet at the time of manufacturing.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pClaimCertPath Path to the claim certificate.
 * @param[in] pClaimCertLabel PKCS #11 label for the claim certificate.
 * @param[in] pClaimPrivKeyPath Path to the claim private key.
 * @param[in] pClaimPrivKeyLabel PKCS #11 label for the claim private key.
 *
 * @return True on success.
 */
bool loadClaimCredentials( CK_SESSION_HANDLE p11Session,
                           const char * pClaimCertPath,
                           const char * pClaimCertLabel,
                           const char * pClaimPrivKeyPath,
                           const char * pClaimPrivKeyLabel );

/**
 * @brief Save the device client certificate into the PKCS #11 module.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pCertificate The certificate to load.
 * @param[in] pLabel PKCS #11 label for the certificate.
 * @param[in] certificateLength Length of #pCertificate.
 *
 * @return True on success.
 */
bool loadCertificate( CK_SESSION_HANDLE p11Session,
                      const char * pCertificate,
                      const char * pLabel,
                      size_t certificateLength );

/**
 * @brief Save the device client certificate into the PKCS #11 module.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pPrivateKey The private key to load.
 * @param[in] pLabel PKCS #11 label for the private key.
 * @param[in] privateKeyLength Length of #pPrivateKey.
 *
 * @return True on success.
 */
bool loadPrivateKey( CK_SESSION_HANDLE p11Session,
                     const char * pPrivateKey,
                     const char * pLabel,
                     size_t privateKeyLength );

/**
 * @brief Close the PKCS #11 session.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 *
 * @return True on success.
 */
bool pkcs11CloseSession( CK_SESSION_HANDLE p11Session );

#endif /* ifndef PKCS11_OPERATIONS_H_ */
