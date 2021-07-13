/*
 * AWS IoT Device SDK for Embedded C 202103.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>

/**
 * @brief Creates the document to be published to the CreateCertificateFromCsr
 * API in order to request a certificate from AWS IoT for the included
 * Certificate Signing Request (CSR).
 *
 * @param[in] pBuffer Buffer into which to write the publish document.
 * @param[in] bufferLength Length of #buffer.
 * @param[in] pCsr The CSR to include in the document.
 * @param[in] csrLength The length of #pCsr.
 * @param[out] pOutLengthWritten The length of the publish document.
 */
bool generateCsrRequest( char * pBuffer,
                         size_t bufferLength,
                         const char * pCsr,
                         size_t csrLength,
                         size_t * pOutLengthWritten );

/**
 * @brief Creates the document to be published to the RegisterThing API in order
 * to activate the provisioned certificate and receive a Thing name.
 *
 * @param[in] pBuffer Buffer into which to write the publish document.
 * @param[in] bufferLength Length of #buffer.
 * @param[in] pCertificateOwnershipToken The certificate's certificate ownership
 * token.
 * @param[in] certificateOwnershipTokenLength Length of #certificateOwnershipToken.
 * @param[out] pOutLengthWritten The length of the publish document.
 */
bool generateRegisterThingRequest( char * pBuffer,
                                   size_t bufferLength,
                                   const char * pCertificateOwnershipToken,
                                   size_t certificateOwnershipTokenLength,
                                   const char * pSerial,
                                   size_t serialLength,
                                   size_t * pOutLengthWritten );

/**
 * @brief Extracts the certificate, certificate ID, and certificate ownership
 * token from a CreateCertificateFromCsr accepted response.
 *
 * @param[in] pResponse The response document.
 * @param[in] length Length of #response.
 * @param[in] pCertificate The buffer to which to write the certificate.
 * @param[in,out] pCertificateLength The length of #certificate. The written
 * length is output here.
 * @param[in] pCertificateId The buffer to which to write the certificate ID.
 * @param[in,out] pCertificateIdLength The length of #certificateId. The written
 * length is output here.
 * @param[in] pOwnershipToken The buffer to which to write the certificate
 * ownership token.
 * @param[in,out] pOwnershipTokenLength The length of #ownershipToken. The written
 * length is output here.
 */
bool parseCsrResponse( const char * pResponse,
                       size_t length,
                       char * pCertificate,
                       size_t * pCertificateLength,
                       char * pCertificateId,
                       size_t * pCertificateIdLength,
                       char * pOwnershipToken,
                       size_t * pOwnershipTokenLength );

/**
 * @brief Extracts the Thing name from a RegisterThing accepted response.
 *
 * @param[in] pResponse The response document.
 * @param[in] length Length of #response.
 * @param[in] pThingNameBuffer The buffer to which to write the Thing name.
 * @param[in,out] pThingNameBufferLength The length of #thingNameBuffer. The written
 * length is output here.
 */
bool parseRegisterThingResponse( const char * pResponse,
                                 size_t length,
                                 char * pThingNameBuffer,
                                 size_t * pThingNameBufferLength );
