/*
 * Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * @file aws_iot_download_cbor_internal.h
 * @brief Macros, enums, variables, and definitions internal to the CBOR module and
 * shared by the testing files.
 */

#ifndef _AWS_IOT_DOWNLOAD_CBOR_INTERNAL_H_
#define _AWS_IOT_DOWNLOAD_CBOR_INTERNAL_H_

/**
 * @brief Message field definitions, per the server specification. These are
 * not part of the library interface but are included here for testability.
 */
#define CBOR_CLIENTTOKEN_KEY          "c"
#define CBOR_FILEID_KEY               "f"
#define CBOR_BLOCKSIZE_KEY            "l"
#define CBOR_BLOCKOFFSET_KEY          "o"
#define CBOR_BLOCKBITMAP_KEY          "b"
#define CBOR_STREAMDESCRIPTION_KEY    "d"
#define CBOR_STREAMFILES_KEY          "r"
#define CBOR_FILESIZE_KEY             "z"
#define CBOR_BLOCKID_KEY              "i"
#define CBOR_BLOCKPAYLOAD_KEY         "p"

#endif /* ifndef _AWS_IOT_DOWNLOAD_CBOR_INTERNAL_H_ */
