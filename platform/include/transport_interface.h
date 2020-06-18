#ifndef TRANSPORT_INTERFACE_H_
#define TRANSPORT_INTERFACE_H_

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
 * @brief Transport interface for reading data on the network.
 *
 * @param[in] pContext Application-defined context.
 * @param[in] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return The number of bytes read or a negative error code.
 */
typedef int32_t ( * TransportRecv_t )( NetworkContext_t pContext,
                                       void * pBuffer,
                                       size_t bytesToRead );

/**
 * @brief Transport interface for sending data over the network.
 *
 * @param[in] pContext Application-defined context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToWrite Number of bytes to write to the network.
 *
 * @return The number of bytes written or a negative error code.
 */
typedef int32_t ( * TransportSend_t )( NetworkContext_t pContext,
                                       const void * pBuffer,
                                       size_t bytesToWrite );

/**
 * @brief The transport layer interface.
 */
typedef struct TransportInterface
{
    TransportRecv_t recv;      /**< Transport receive interface. */
    TransportSend_t send;      /**< Transport send interface. */
    NetworkContext_t pContext; /**< Application-defined transport interface context. */
} TransportInterface_t;

#endif /* ifndef TRANSPORT_INTERFACE_H_ */
