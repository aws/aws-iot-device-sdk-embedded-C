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

/**
 * @file network_interface.h
 * @brief Network interface definition for MQTT client.
 *
 * Defines an interface to the TLS layer to be used by the MQTT client.
 * Starting point for porting the SDK to the networking layer of a new platform.
 */

#ifndef __NETWORK_INTERFACE_H_
#define __NETWORK_INTERFACE_H_

/**
 * @brief Network Type
 *
 * Defines a type for the network struct.  See structure definition below.
 */
typedef struct Network Network;

/**
 * @brief TLS Connection Parameters
 *
 * Defines a type containing TLS specific parameters to be passed down to the
 * TLS networking layer to create a TLS secured socket.
 */
typedef struct{
	char* pRootCALocation;				///< Pointer to string containing the filename (including path) of the root CA file.
	char* pDeviceCertLocation;			///< Pointer to string containing the filename (including path) of the device certificate.
	char* pDevicePrivateKeyLocation;	///< Pointer to string containing the filename (including path) of the device private key file.
	char* pDestinationURL;				///< Pointer to string containing the endpoint of the MQTT service.
	int DestinationPort;				///< Integer defining the connection port of the MQTT service.
	unsigned int timeout_ms;			///< Unsigned integer defining the TLS handshake timeout value in milliseconds.
	unsigned char ServerVerificationFlag;	///< Boolean.  True = perform server certificate hostname validation.  False = skip validation \b NOT recommended.
}TLSConnectParams;

/**
 * @brief Network Structure
 *
 * Structure for defining a network connection.
 */
struct Network{
	int my_socket;	///< Integer holding the socket file descriptor
	int (*mqttread) (Network*, unsigned char*, int, int);	///< Function pointer pointing to the network function to read from the network
	int (*mqttwrite) (Network*, unsigned char*, int, int);	///< Function pointer pointing to the network function to write to the network
	void (*disconnect) (Network*);		///< Function pointer pointing to the network function to disconnect from the network
};

/**
 * @brief Initialize the TLS implementation
 *
 * Perform any initialization required by the TLS layer.
 * Connects the interface to implementation by setting up
 * the network layer function pointers to platform implementations.
 *
 * @param pNetwork - Pointer to a Network struct defining the network interface.
 * @return integer defining successful initialization or TLS error
 */
int iot_tls_init(Network *pNetwork);

/**
 * @brief Create a TLS socket and open the connection
 *
 * Creates an open socket connection including TLS handshake.
 *
 * @param pNetwork - Pointer to a Network struct defining the network interface.
 * @param TLSParams - TLSConnectParams defines the properties of the TLS connection.
 * @return integer - successful connection or TLS error
 */
int iot_tls_connect(Network *pNetwork, TLSConnectParams TLSParams);

/**
 * @brief Write bytes to the network socket
 *
 * @param Network - Pointer to a Network struct defining the network interface.
 * @param unsigned char pointer - buffer to write to socket
 * @param integer - number of bytes to write
 * @param integer - write timeout value in milliseconds
 * @return integer - number of bytes written or TLS error
 */
int iot_tls_write(Network*, unsigned char*, int, int);

/**
 * @brief Read bytes from the network socket
 *
 * @param Network - Pointer to a Network struct defining the network interface.
 * @param unsigned char pointer - pointer to buffer where read bytes should be copied
 * @param integer - number of bytes to read
 * @param integer - read timeout value in milliseconds
 * @return integer - number of bytes read or TLS error
 */
int iot_tls_read(Network*, unsigned char*, int, int);

/**
 * @brief Disconnect from network socket
 *
 * @param Network - Pointer to a Network struct defining the network interface.
 */
void iot_tls_disconnect(Network *pNetwork);

/**
 * @brief Perform any tear-down or cleanup of TLS layer
 *
 * Called to cleanup any resources required for the TLS layer.
 *
 * @param Network - Pointer to a Network struct defining the network interface.
 * @return integer - successful cleanup or TLS error
 */
int iot_tls_destroy(Network *pNetwork);

#endif //__NETWORK_INTERFACE_H_
