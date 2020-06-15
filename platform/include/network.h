#ifndef NETWORK_H_
#define NETWORK_H_

#include <stdint.h>
#include <stddef.h>

/**
 * @brief The NetworkContext is an incomplete type. The application must
 * define NetworkContext to the type of their network context. This context
 * is passed into the network interface functions.
 */
struct NetworkContext;
typedef struct NetworkContext * NetworkContext_t;

/**
 * @ingroup platform_datatypes_enums
 * @brief Return codes for [network functions](@ref platform_network_functions).
 */
typedef enum NetworkStatus
{
    NETWORK_SUCCESS = 0,         /**< Function successfully completed. */
    NETWORK_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    NETWORK_INVALID_CREDENTIALS, /**< Provided certificates or key were invalid. */
    NETWORK_CONNECT_FAILURE,     /**< Initial connection to the server failed. */
    NETWORK_DNS_FAILURE,         /**< Resolving hostname of server failed. */
    NETWORK_INTERNAL_ERROR,      /**< Generic failure not covered by other values. */
    NETWORK_NO_MEMORY,           /**< Memory allocation failed. */
    NETWORK_SYSTEM_ERROR         /**< An error occurred when calling a system API. */
} NetworkStatus_t;

/**
 * @ingroup platform_datatypes_enums
 * @brief Disconnect reasons for [the network close callback](@ref platform_network_function_closecallback).
 */
typedef enum NetworkCloseReason
{
    NETWORK_NOT_CLOSED = 0,    /**< Not closed, still open */
    NETWORK_SERVER_CLOSED,     /**< Server closed connection. */
    NETWORK_TRANSPORT_FAILURE, /**< Transport failed. */
    NETWORK_CLIENT_CLOSED,     /**< Client closed connection. */
    NETWORK_UNKNOWN_CLOSED     /**< Unknown close reason. */
} NetworkCloseReason_t;

/**
 * @ingroup platform_datatypes_paramstructs
 * @brief Information on the remote server for connection setup.
 *
 * May be passed to #IotNetworkInterface_t.create as `pConnectionInfo`. This
 * structure contains commonly-used parameters, but may be replaced with an
 * alternative.
 */
typedef struct NetworkServerInfo
{
    const char * pHostName; /**< @brief Server host name. Must be NULL-terminated. */
    size_t hostNameLength;  /**< @brief Length associated with #NetworkServerInfo.pHostName. */
    uint16_t port;          /**< @brief Server port in host-order. */
} NetworkServerInfo_t;

/**
 * @ingroup platform_datatypes_paramstructs
 * @brief Contains the credentials necessary for connection setup.
 *
 * May be passed to #IotNetworkInterface_t.create as `pCredentialInfo`. This
 * structure contains commonly-used parameters, but may be replaced with an
 * alternative.
 */
struct NetworkCredentials
{
    /**
     * @brief Set this to a non-NULL value to use ALPN.
     *
     * This string must be NULL-terminated.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char * pAlpnProtos;

    /**
     * @brief Set this to a non-zero value to use TLS max fragment length
     * negotiation (TLS MFLN).
     *
     * @note The network stack may have a minimum value for this parameter and
     * may return an error if this parameter is too small.
     */
    size_t maxFragmentLength;

    /**
     * @brief Flags to configure the TLS connection.
     */
    uint16_t flags;

    const char * pRootCaPath;     /**< @brief Filepath string to the trusted server root certificate. */
    size_t rootCaPathLen;         /**< @brief Length associated with #NetworkCredentials.pRootCa. */
    const char * pClientCertPath; /**< @brief Filepath string to the client certificate. */
    size_t clientCertPathLen;     /**< @brief Length associated with #NetworkCredentials.pClientCert. */
    const char * pPrivateKeyPath; /**< @brief Filepath string to the client certificate's private key. */
    size_t privateKeyPathLen;     /**< @brief Length associated with #NetworkCredentials.pPrivateKey. */
};

#endif /* ifndef NETWORK_H_ */
