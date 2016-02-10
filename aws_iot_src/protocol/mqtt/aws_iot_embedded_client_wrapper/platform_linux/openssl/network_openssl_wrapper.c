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

#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <sys/select.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netdb.h>

#include "aws_iot_error.h"
#include "aws_iot_log.h"
#include "network_interface.h"
#include "openssl_hostname_validation.h"

static SSL_CTX *pSSLContext;
static SSL *pSSLHandle;
static int server_TCPSocket;
static char* pDestinationURL;

static int Create_TCPSocket(void);
static IoT_Error_t Connect_TCPSocket(int socket_fd, char *pURLString, int port);
static IoT_Error_t setSocketToNonBlocking(int server_fd);
static IoT_Error_t ConnectOrTimeoutOrExitOnError(SSL *pSSL, int timeout_ms);
static IoT_Error_t ReadOrTimeoutOrExitOnError(SSL *pSSL, unsigned char *msg, int totalLen, int timeout_ms);

int iot_tls_init(Network *pNetwork) {

	IoT_Error_t ret_val = NONE_ERROR;
	const SSL_METHOD *method;

	OpenSSL_add_all_algorithms();
	ERR_load_BIO_strings();
	ERR_load_crypto_strings();
	SSL_load_error_strings();

	if (SSL_library_init() < 0) {
		ret_val = SSL_INIT_ERROR;
	}

	method = TLSv1_2_method();

	if ((pSSLContext = SSL_CTX_new(method)) == NULL) {
		ERROR(" SSL INIT Failed - Unable to create SSL Context");
		ret_val = SSL_INIT_ERROR;
	}

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

int tls_server_certificate_verify(int preverify_ok, X509_STORE_CTX *pX509CTX){
	// preverify_ok
	// 0 ==> Fail
	// 1 ==> Pass
	int verification_return = 0;

	//last certificate(depth = 0) is the one provided by the Server
	if((X509_STORE_CTX_get_error_depth(pX509CTX) == 0) && (preverify_ok == 1)){
		X509 *pX509Cert;
		HostnameValidationResult result;
		pX509Cert = X509_STORE_CTX_get_current_cert(pX509CTX);
		result = validate_hostname(pDestinationURL, pX509Cert);
		if(MatchFound == result){
			verification_return = 1;
		}
	}
	else{
		verification_return = preverify_ok;
	}

	return verification_return;
}

int iot_tls_connect(Network *pNetwork, TLSConnectParams params) {

	IoT_Error_t ret_val = NONE_ERROR;
	int connect_status = 0;

	server_TCPSocket = Create_TCPSocket();
	if(-1 == server_TCPSocket){
		ret_val = TCP_SETUP_ERROR;
		return ret_val;
	}

	if (!SSL_CTX_load_verify_locations(pSSLContext, params.pRootCALocation, NULL)) {
		ERROR(" Root CA Loading error");
		ret_val = SSL_CERT_ERROR;
	}

	if (!SSL_CTX_use_certificate_file(pSSLContext, params.pDeviceCertLocation, SSL_FILETYPE_PEM)) {
		ERROR(" Device Certificate Loading error");
		ret_val = SSL_CERT_ERROR;
	}

	if(1 != SSL_CTX_use_PrivateKey_file(pSSLContext, params.pDevicePrivateKeyLocation, SSL_FILETYPE_PEM)){
		ERROR(" Device Private Key Loading error");
		ret_val = SSL_CERT_ERROR;
	}
	if(params.ServerVerificationFlag){
		SSL_CTX_set_verify(pSSLContext, SSL_VERIFY_PEER, tls_server_certificate_verify);
	}
	else{
		SSL_CTX_set_verify(pSSLContext, SSL_VERIFY_PEER, NULL);
	}

	pSSLHandle = SSL_new(pSSLContext);

	pDestinationURL = params.pDestinationURL;
	ret_val = Connect_TCPSocket(server_TCPSocket, params.pDestinationURL, params.DestinationPort);
	if(NONE_ERROR != ret_val){
		ERROR(" TCP Connection error");
		return ret_val;
	}

	SSL_set_fd(pSSLHandle, server_TCPSocket);

	if(ret_val == NONE_ERROR){
		ret_val = setSocketToNonBlocking(server_TCPSocket);
		if(ret_val != NONE_ERROR){
			ERROR(" Unable to set the socket to Non-Blocking");
		}
	}

	if(NONE_ERROR == ret_val){
		ret_val = ConnectOrTimeoutOrExitOnError(pSSLHandle, params.timeout_ms);
		if(X509_V_OK != SSL_get_verify_result(pSSLHandle)){
			ERROR(" Server Certificate Verification failed");
			ret_val = SSL_CONNECT_ERROR;
		}
		else{
			// ensure you have a valid certificate returned, otherwise no certificate exchange happened
			if(NULL == SSL_get_peer_certificate(pSSLHandle)){
				ERROR(" No certificate exchange happened");
				ret_val = SSL_CONNECT_ERROR;
			}
		}
	}
	return ret_val;
}

int iot_tls_write(Network *pNetwork, unsigned char *pMsg, int len, int timeout_ms){

	return WriteOrTimeoutOrExitOnError(pSSLHandle, pMsg, len, timeout_ms);
}

int iot_tls_read(Network *pNetwork, unsigned char *pMsg, int len, int timeout_ms) {
	return ReadOrTimeoutOrExitOnError(pSSLHandle, pMsg, len, timeout_ms);
}

void iot_tls_disconnect(Network *pNetwork){
	SSL_shutdown(pSSLHandle);
	close(server_TCPSocket);
}

int iot_tls_destroy(Network *pNetwork) {
	SSL_free(pSSLHandle);
	SSL_CTX_free(pSSLContext);
	return 0;
}

int Create_TCPSocket(void) {
	int sockfd;
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	return sockfd;
}

IoT_Error_t Connect_TCPSocket(int socket_fd, char *pURLString, int port) {
	IoT_Error_t ret_val = TCP_CONNECT_ERROR;
	int connect_status = -1;
	struct hostent *host;
	struct sockaddr_in dest_addr;

	host = gethostbyname(pURLString);

	if (NULL != host) {
		dest_addr.sin_family = AF_INET;
		dest_addr.sin_port = htons(port);
		dest_addr.sin_addr.s_addr = *(long*) (host->h_addr);
		memset(&(dest_addr.sin_zero), '\0', 8);

		connect_status = connect(socket_fd, (struct sockaddr *) &dest_addr,
				sizeof(struct sockaddr));
		if (-1 != connect_status) {
			ret_val = NONE_ERROR;
		}
	}
	return ret_val;
}

IoT_Error_t setSocketToNonBlocking( server_fd) {

	int flags, status;
	IoT_Error_t ret_val = NONE_ERROR;

	flags = fcntl(server_TCPSocket, F_GETFL, 0);
	// set underlying socket to non blocking
	if (flags < 0) {
		ret_val = TCP_CONNECT_ERROR;
	}

	status = fcntl(server_TCPSocket, F_SETFL, flags | O_NONBLOCK);
	if (status < 0) {
		ERROR("fcntl - %s", strerror(errno));
		ret_val = TCP_CONNECT_ERROR;
	}

	return ret_val;
}

IoT_Error_t ConnectOrTimeoutOrExitOnError(SSL *pSSL, int timeout_ms){

	enum{
		SSL_CONNECTED = 1,
		SELECT_TIMEOUT = 0,
		SELECT_ERROR = -1
	};

	IoT_Error_t ret_val = NONE_ERROR;
	int rc = 0;
	fd_set readFds;
	fd_set writeFds;
	struct timeval timeout = { timeout_ms / 1000, (timeout_ms % 1000) * 1000 };
	int errorCode = 0;
	int select_retCode = SELECT_TIMEOUT;

	do{
		rc = SSL_connect(pSSL);

		if(SSL_CONNECTED == rc){
			ret_val = NONE_ERROR;
			break;
		}

		errorCode = SSL_get_error(pSSL, rc);

		if(errorCode == SSL_ERROR_WANT_READ){
			FD_ZERO(&readFds);
			FD_SET(server_TCPSocket, &readFds);
			select_retCode = select(server_TCPSocket + 1, (void *) &readFds, NULL, NULL, &timeout);
			if (SELECT_TIMEOUT == select_retCode) {
				ERROR(" SSL Connect time out while waiting for read");
				ret_val = SSL_CONNECT_TIMEOUT_ERROR;
			} else if (SELECT_ERROR == select_retCode) {
				ERROR(" SSL Connect Select error for read %d", select_retCode);
				ret_val = SSL_CONNECT_ERROR;
			}
		}

		else if(errorCode == SSL_ERROR_WANT_WRITE){
			FD_ZERO(&writeFds);
			FD_SET(server_TCPSocket, &writeFds);
			select_retCode = select(server_TCPSocket + 1, NULL, (void *) &writeFds, NULL, &timeout);
			if (SELECT_TIMEOUT == select_retCode) {
				ERROR(" SSL Connect time out while waiting for write");
				ret_val = SSL_CONNECT_TIMEOUT_ERROR;
			} else if (SELECT_ERROR == select_retCode) {
				ERROR(" SSL Connect Select error for write %d", select_retCode);
				ret_val = SSL_CONNECT_ERROR;
			}
		}

		else{
			ret_val = SSL_CONNECT_ERROR;
		}

	}while(SSL_CONNECT_ERROR != ret_val && SSL_CONNECT_TIMEOUT_ERROR != ret_val);

	return ret_val;
}

IoT_Error_t WriteOrTimeoutOrExitOnError(SSL *pSSL, unsigned char *msg, int totalLen, int timeout_ms){


	IoT_Error_t errorStatus = NONE_ERROR;

	fd_set writeFds;
	enum{
		SELECT_TIMEOUT = 0,
		SELECT_ERROR = -1
	};
	int errorCode = 0;
	int select_retCode;
	int writtenLength = 0;
	int rc = 0;
	int returnCode = 0;
	struct timeval timeout = { timeout_ms / 1000, (timeout_ms % 1000) * 1000 };

	do{
		rc = SSL_write(pSSL, msg, totalLen);

		errorCode = SSL_get_error(pSSL, rc);

		if(0 < rc){
			writtenLength += rc;
		}

		else if (errorCode == SSL_ERROR_WANT_WRITE) {
			FD_ZERO(&writeFds);
			FD_SET(server_TCPSocket, &writeFds);
			select_retCode = select(server_TCPSocket + 1, NULL, (void *) &writeFds, NULL, &timeout);
			if (SELECT_TIMEOUT == select_retCode) {
				errorStatus = SSL_WRITE_TIMEOUT_ERROR;
			} else if (SELECT_ERROR == select_retCode) {
				errorStatus = SSL_WRITE_ERROR;
			}
		}

		else{
			errorStatus = SSL_WRITE_ERROR;
		}

	}while(SSL_WRITE_ERROR != errorStatus && SSL_WRITE_TIMEOUT_ERROR != errorStatus && writtenLength < totalLen);

	if(NONE_ERROR == errorStatus){
		returnCode = writtenLength;
	}
	else{
		returnCode = errorStatus;
	}

	return returnCode;
}

IoT_Error_t ReadOrTimeoutOrExitOnError(SSL *pSSL, unsigned char *msg, int totalLen, int timeout_ms){


	IoT_Error_t errorStatus = NONE_ERROR;

	fd_set readFds;
	enum{
		SELECT_TIMEOUT = 0,
		SELECT_ERROR = -1
	};
	int errorCode = 0;
	int select_retCode;
	int readLength = 0;
	int rc = 0;
	int returnCode = 0;
	struct timeval timeout = { timeout_ms / 1000, (timeout_ms % 1000) * 1000 };

	do{
		rc = SSL_read(pSSL, msg, totalLen);
		errorCode = SSL_get_error(pSSL, rc);

		if(0 < rc){
			readLength += rc;
		}

		else if (errorCode == SSL_ERROR_WANT_READ) {
			FD_ZERO(&readFds);
			FD_SET(server_TCPSocket, &readFds);
			select_retCode = select(server_TCPSocket + 1, (void *) &readFds, NULL, NULL, &timeout);
			if (SELECT_TIMEOUT == select_retCode) {
				errorStatus = SSL_READ_TIMEOUT_ERROR;
			} else if (SELECT_ERROR == select_retCode) {
				errorStatus = SSL_READ_ERROR;
			}
		}

		else{
			errorStatus = SSL_READ_ERROR;
		}

	}while(SSL_READ_ERROR != errorStatus && SSL_READ_TIMEOUT_ERROR != errorStatus && readLength < totalLen);

	if(NONE_ERROR == errorStatus){
		returnCode = readLength;
	}
	else{
		returnCode = errorStatus;
	}

	return returnCode;
}
