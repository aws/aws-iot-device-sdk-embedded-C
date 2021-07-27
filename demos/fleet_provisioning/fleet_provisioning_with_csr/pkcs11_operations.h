/*
 * AWS IoT Device SDK for Embedded C 202103.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include <stdbool.h>

/* corePKCS11 include. */
#include "core_pkcs11.h"
#include "core_pkcs11_config.h"

/**
 * @brief Loads the claim credentials into the PKCS #11 module.
 *
 * Note: This function is for demonstration purposes, and the claim credentials
 * should be securely stored for production devices.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 */
bool loadClaimCredentials( CK_SESSION_HANDLE p11Session );

/**
 * @brief Generate new keys and sign a CSR for them with the PKCS #11 module.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[out] pCsrBuffer The buffer to write the CSR to.
 * @param[in] csrBufferLength Length of #pCsrBuffer.
 * @param[out] pOutCsrLength The length of the written CSR.
 */
bool generateKeyAndCsr( CK_SESSION_HANDLE p11Session,
                        char * pCsrBuffer,
                        size_t csrBufferLength,
                        size_t * pOutCsrLength );

/**
 * @brief Save the device client certificate into the PKCS #11 module.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 * @param[in] pCertificate The certificate to save.
 * @param[in] certificateLength Length of #pCertificate.
 */
bool loadCertificate( CK_SESSION_HANDLE p11Session,
                      char * pCertificate,
                      size_t certificateLength );

/**
 * @brief Close the PKCS #11 session.
 *
 * @param[in] p11Session The PKCS #11 session to use.
 */
bool pkcs11CloseSession( CK_SESSION_HANDLE p11Session );

#endif /* ifndef PKCS11_OPERATIONS_H_ */
