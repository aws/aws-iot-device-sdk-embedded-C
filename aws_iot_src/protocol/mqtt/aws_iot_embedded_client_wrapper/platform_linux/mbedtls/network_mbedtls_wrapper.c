/*
 * Copyright 2010-2015 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <stdbool.h>
#include <string.h>

#include "aws_iot_error.h"
#include "aws_iot_log.h"
#include "network_interface.h"
#include "mbedtls/config.h"

#include "mbedtls/net.h"
#include "mbedtls/ssl.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/certs.h"
#include "mbedtls/x509.h"
#include "mbedtls/error.h"
#include "mbedtls/debug.h"
#include "mbedtls/timing.h"

/*
 * This is a function to do further verification if needed on the cert received
 */

static int myCertVerify(void *data, mbedtls_x509_crt *crt, int depth, uint32_t *flags) {
	char buf[1024];
	((void) data);

	DEBUG("\nVerify requested for (Depth %d):\n", depth);
	mbedtls_x509_crt_info(buf, sizeof(buf) - 1, "", crt);
	DEBUG("%s", buf);

	if ((*flags) == 0) {
		DEBUG("  This certificate has no flags\n");
	} else {
		DEBUG(buf, sizeof(buf), "  ! ", *flags); DEBUG("%s\n", buf);
	}

	return (0);
}

static int ret = 0, i;
static mbedtls_entropy_context entropy;
static mbedtls_ctr_drbg_context ctr_drbg;
static mbedtls_ssl_context ssl;
static mbedtls_ssl_config conf;
static uint32_t flags;
static mbedtls_x509_crt cacert;
static mbedtls_x509_crt clicert;
static mbedtls_pk_context pkey;
static mbedtls_net_context server_fd;

int iot_tls_init(Network *pNetwork) {
	IoT_Error_t ret_val = NONE_ERROR;
	const char *pers = "aws_iot_tls_wrapper";
	unsigned char buf[MBEDTLS_SSL_MAX_CONTENT_LEN + 1];

	mbedtls_net_init(&server_fd);
	mbedtls_ssl_init(&ssl);
	mbedtls_ssl_config_init(&conf);
	mbedtls_ctr_drbg_init(&ctr_drbg);
	mbedtls_x509_crt_init(&cacert);
	mbedtls_x509_crt_init(&clicert);
	mbedtls_pk_init(&pkey);

	DEBUG("\n  . Seeding the random number generator...");
	mbedtls_entropy_init(&entropy);
	if ((ret_val = mbedtls_ctr_drbg_seed(&ctr_drbg, mbedtls_entropy_func, &entropy, (const unsigned char *) pers,
			strlen(pers))) != 0) {
		ERROR(" failed\n  ! mbedtls_ctr_drbg_seed returned -0x%x\n", -ret);
		return ret_val;
	} DEBUG("ok\n");

	pNetwork->my_socket = 0;
	pNetwork->connect = iot_tls_connect;
	pNetwork->mqttread = iot_tls_read;
	pNetwork->mqttwrite = iot_tls_write;
	pNetwork->disconnect = iot_tls_disconnect;
	pNetwork->isConnected = iot_tls_is_connected;
	pNetwork->destroy = iot_tls_destroy;

	return ret_val;
}

int iot_tls_is_connected(Network *pNetwork) {
	/* Use this to add implementation which can check for physical layer disconnect */
	return 1;
}

int iot_tls_connect(Network *pNetwork, TLSConnectParams params) {
	const char *pers = "aws_iot_tls_wrapper";
	unsigned char buf[MBEDTLS_SSL_MAX_CONTENT_LEN + 1];

	DEBUG("  . Loading the CA root certificate ...");
	ret = mbedtls_x509_crt_parse_file(&cacert, params.pRootCALocation);
	if (ret < 0) {
		ERROR(" failed\n  !  mbedtls_x509_crt_parse returned -0x%x\n\n", -ret);
		return ret;
	} DEBUG(" ok (%d skipped)\n", ret);

	DEBUG("  . Loading the client cert. and key...");
	ret = mbedtls_x509_crt_parse_file(&clicert, params.pDeviceCertLocation);
	if (ret != 0) {
		ERROR(" failed\n  !  mbedtls_x509_crt_parse returned -0x%x\n\n", -ret);
		return ret;
	}

	ret = mbedtls_pk_parse_keyfile(&pkey, params.pDevicePrivateKeyLocation, "");
	if (ret != 0) {
		ERROR(" failed\n  !  mbedtls_pk_parse_key returned -0x%x\n\n", -ret);
		return ret;
	} DEBUG(" ok\n");
	char portBuffer[6];
	sprintf(portBuffer, "%d", params.DestinationPort); DEBUG("  . Connecting to %s/%s...", params.pDestinationURL, portBuffer);
	if ((ret = mbedtls_net_connect(&server_fd, params.pDestinationURL, portBuffer, MBEDTLS_NET_PROTO_TCP)) != 0) {
		ERROR(" failed\n  ! mbedtls_net_connect returned -0x%x\n\n", -ret);
		return ret;
	}

	ret = mbedtls_net_set_block(&server_fd);
	if (ret != 0) {
		ERROR(" failed\n  ! net_set_(non)block() returned -0x%x\n\n", -ret);
		return ret;
	} DEBUG(" ok\n");

	DEBUG("  . Setting up the SSL/TLS structure...");
	if ((ret = mbedtls_ssl_config_defaults(&conf, MBEDTLS_SSL_IS_CLIENT, MBEDTLS_SSL_TRANSPORT_STREAM,
			MBEDTLS_SSL_PRESET_DEFAULT)) != 0) {
		ERROR(" failed\n  ! mbedtls_ssl_config_defaults returned -0x%x\n\n", -ret);
		return ret;
	}

	mbedtls_ssl_conf_verify(&conf, myCertVerify, NULL);
	if (params.ServerVerificationFlag == true) {
		mbedtls_ssl_conf_authmode(&conf, MBEDTLS_SSL_VERIFY_REQUIRED);
	} else {
		mbedtls_ssl_conf_authmode(&conf, MBEDTLS_SSL_VERIFY_OPTIONAL);
	}
	mbedtls_ssl_conf_rng(&conf, mbedtls_ctr_drbg_random, &ctr_drbg);

	mbedtls_ssl_conf_ca_chain(&conf, &cacert, NULL);
	if ((ret = mbedtls_ssl_conf_own_cert(&conf, &clicert, &pkey)) != 0) {
		ERROR(" failed\n  ! mbedtls_ssl_conf_own_cert returned %d\n\n", ret);
		return ret;
	}

	mbedtls_ssl_conf_read_timeout(&conf, params.timeout_ms);

	if ((ret = mbedtls_ssl_setup(&ssl, &conf)) != 0) {
		ERROR(" failed\n  ! mbedtls_ssl_setup returned -0x%x\n\n", -ret);
		return ret;
	}
	if ((ret = mbedtls_ssl_set_hostname(&ssl, params.pDestinationURL)) != 0) {
		ERROR(" failed\n  ! mbedtls_ssl_set_hostname returned %d\n\n", ret);
		return ret;
	}
	mbedtls_ssl_set_bio(&ssl, &server_fd, mbedtls_net_send, NULL, mbedtls_net_recv_timeout);
	DEBUG(" ok\n");

	DEBUG("  . Performing the SSL/TLS handshake...");
	while ((ret = mbedtls_ssl_handshake(&ssl)) != 0) {
		if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
			ERROR(" failed\n  ! mbedtls_ssl_handshake returned -0x%x\n", -ret);
			if (ret == MBEDTLS_ERR_X509_CERT_VERIFY_FAILED) {
				ERROR("    Unable to verify the server's certificate. "
						"Either it is invalid,\n"
						"    or you didn't set ca_file or ca_path "
						"to an appropriate value.\n"
						"    Alternatively, you may want to use "
						"auth_mode=optional for testing purposes.\n");
			}
			return ret;
		}
	}

	DEBUG(" ok\n    [ Protocol is %s ]\n    [ Ciphersuite is %s ]\n", mbedtls_ssl_get_version(&ssl), mbedtls_ssl_get_ciphersuite(&ssl));
	if ((ret = mbedtls_ssl_get_record_expansion(&ssl)) >= 0) {
		DEBUG("    [ Record expansion is %d ]\n", ret);
	} else {
		DEBUG("    [ Record expansion is unknown (compression) ]\n");
	}

	DEBUG("  . Verifying peer X.509 certificate...");

	if (params.ServerVerificationFlag == true) {
		if ((flags = mbedtls_ssl_get_verify_result(&ssl)) != 0) {
			char vrfy_buf[512];
			ERROR(" failed\n");
			mbedtls_x509_crt_verify_info(vrfy_buf, sizeof(vrfy_buf), "  ! ", flags);
			ERROR("%s\n", vrfy_buf);
		} else {
			DEBUG(" ok\n");
			ret = NONE_ERROR;
		}
	} else {
		DEBUG(" Server Verification skipped\n");
		ret = NONE_ERROR;
	}

	if (mbedtls_ssl_get_peer_cert(&ssl) != NULL) {
		DEBUG("  . Peer certificate information    ...\n");
		mbedtls_x509_crt_info((char *) buf, sizeof(buf) - 1, "      ", mbedtls_ssl_get_peer_cert(&ssl));
		DEBUG("%s\n", buf);
	}

	mbedtls_ssl_conf_read_timeout(&conf, 10);

	return ret;
}

int iot_tls_write(Network *pNetwork, unsigned char *pMsg, int len, int timeout_ms) {

	int written;
	int frags;

	for (written = 0, frags = 0; written < len; written += ret, frags++) {
		while ((ret = mbedtls_ssl_write(&ssl, pMsg + written, len - written)) <= 0) {
			if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
				ERROR(" failed\n  ! mbedtls_ssl_write returned -0x%x\n\n", -ret);
				return ret;
			}
		}
	}
	return written;
}

int iot_tls_read(Network *pNetwork, unsigned char *pMsg, int len, int timeout_ms) {
	int rxLen = 0;
	bool isErrorFlag = false;
	bool isCompleteFlag = false;

//	mbedtls_ssl_conf_read_timeout(&conf, timeout_ms);

	do {
		ret = mbedtls_ssl_read(&ssl, pMsg, len);
		if (ret > 0) {
			rxLen += ret;
		} else if (ret != MBEDTLS_ERR_SSL_WANT_READ) {
			isErrorFlag = true;
		}
		if (rxLen >= len) {
			isCompleteFlag = true;
		}
	} while (!isErrorFlag && !isCompleteFlag);

	return ret;
}

void iot_tls_disconnect(Network *pNetwork) {
	do {
		ret = mbedtls_ssl_close_notify(&ssl);
	} while (ret == MBEDTLS_ERR_SSL_WANT_WRITE);
}

int iot_tls_destroy(Network *pNetwork) {

	mbedtls_net_free(&server_fd);

	mbedtls_x509_crt_free(&clicert);
	mbedtls_x509_crt_free(&cacert);
	mbedtls_pk_free(&pkey);
	mbedtls_ssl_free(&ssl);
	mbedtls_ssl_config_free(&conf);
	mbedtls_ctr_drbg_free(&ctr_drbg);
	mbedtls_entropy_free(&entropy);

	return 0;
}
