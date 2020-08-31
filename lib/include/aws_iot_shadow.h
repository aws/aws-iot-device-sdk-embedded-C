/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @file aws_iot_shadow.h
 * @brief User-facing functions and structs of the Shadow library.
 */

#ifndef _AWS_IOT_SHADOW_H_
#define _AWS_IOT_SHADOW_H_

/* Build using a config header, if provided. */
#ifdef AWS_IOT_CONFIG_FILE
    #include AWS_IOT_CONFIG_FILE
#endif

/* MQTT include. */
#include "aws_iot_mqtt.h"

/*--------------------------- Shadow handle types ---------------------------*/

/**
 * @handles{shadow,Shadow library}
 */

/**
 * @ingroup shadow_datatypes_handles
 * @brief Opaque handle that references an in-progress Shadow operation.
 *
 * Set as an output parameter of @ref shadow_function_delete, @ref shadow_function_get,
 * and @ref shadow_function_update. These functions send a message to the Shadow
 * service requesting a Shadow operation; the result of this operation is unknown
 * until the Shadow service sends a response. Therefore, this handle serves as a
 * reference to Shadow operations awaiting a response from the Shadow service.
 *
 * This reference will be valid from the successful return of @ref shadow_function_delete,
 * @ref shadow_function_get, or @ref shadow_function_update. The reference becomes
 * invalid once the [completion callback](@ref AwsIotShadowCallbackInfo_t) is invoked,
 * or @ref shadow_function_wait returns.
 *
 * @initializer{AwsIotShadowReference_t,AWS_IOT_SHADOW_REFERENCE_INITIALIZER}
 *
 * @see @ref shadow_function_wait and #AWS_IOT_SHADOW_FLAG_WAITABLE for waiting on
 * a reference. #AwsIotShadowCallbackInfo_t and #AwsIotShadowCallbackParam_t for an
 * asynchronous notification of completion.
 */
typedef void * AwsIotShadowReference_t;

/*------------------------- Shadow enumerated types -------------------------*/

/**
 * @enums{shadow,Shadow library}
 */

/**
 * @ingroup shadow_datatypes_enums
 * @brief Return codes of [Shadow functions](@ref shadow_functions).
 *
 * The function @ref shadow_function_strerror can be used to get a return code's
 * description.
 *
 * The values between 400 (#AWS_IOT_SHADOW_BAD_REQUEST) and 500
 * (#AWS_IOT_SHADOW_SERVER_ERROR) may be returned by the Shadow service when it
 * rejects a Shadow operation. See [this page]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-error-messages.html)
 * for more information.
 */
typedef enum AwsIotShadowError
{
    /**
     * @brief Shadow operation completed successfully.
     *
     * Functions that may return this value:
     * - @ref shadow_function_init
     * - @ref shadow_function_wait
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     * - @ref shadow_function_removepersistentsubscriptions
     *
     * Will also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     * when successful.
     */
    AWS_IOT_SHADOW_SUCCESS,

    /**
     * @brief Shadow operation queued, awaiting result.
     *
     * Functions that may return this value:
     * - @ref shadow_function_delete
     * - @ref shadow_function_get
     * - @ref shadow_function_update
     */
    AWS_IOT_SHADOW_STATUS_PENDING,

    /**
     * @brief Initialization failed.
     *
     * Functions that may return this value:
     * - @ref shadow_function_init
     */
    AWS_IOT_SHADOW_INIT_FAILED,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref shadow_function_delete and @ref shadow_function_timeddelete
     * - @ref shadow_function_get and @ref shadow_function_timedget
     * - @ref shadow_function_update and @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_BAD_PARAMETER,

    /**
     * @brief Shadow operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref shadow_function_delete and @ref shadow_function_timeddelete
     * - @ref shadow_function_get and @ref shadow_function_timedget
     * - @ref shadow_function_update and @ref shadow_function_timedupdate
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_NO_MEMORY,

    /**
     * @brief Shadow operation failed because of failure in MQTT library.
     *
     * Check the Shadow library logs for the error code returned by the MQTT
     * library.
     *
     * Functions that may return this value:
     * - @ref shadow_function_delete and @ref shadow_function_timeddelete
     * - @ref shadow_function_get and @ref shadow_function_timedget
     * - @ref shadow_function_update and @ref shadow_function_timedupdate
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     * - @ref shadow_function_removepersistentsubscriptions
     */
    AWS_IOT_SHADOW_MQTT_ERROR,

    /**
     * @brief Reponse received from Shadow service not understood.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_BAD_RESPONSE,

    /**
     * @brief A blocking Shadow operation timed out.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     */
    AWS_IOT_SHADOW_TIMEOUT,

    /**
     * @brief Shadow operation rejected: Bad request.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_BAD_REQUEST = 400,

    /**
     * @brief Shadow operation rejected: Unauthorized.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_UNAUTHORIZED = 401,

    /**
     * @brief Shadow operation rejected: Forbidden.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_FORBIDDEN = 403,

    /**
     * @brief Shadow operation rejected: Thing not found.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_NOT_FOUND = 404,

    /**
     * @brief Shadow operation rejected: Version conflict.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_CONFLICT = 409,

    /**
     * @brief Shadow operation rejected: The payload exceeds the maximum size
     * allowed.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_TOO_LARGE = 413,

    /**
     * @brief Shadow operation rejected: Unsupported document encoding; supported
     * encoding is UTF-8.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_UNSUPPORTED = 415,

    /**
     * @brief Shadow operation rejected: The Device Shadow service will generate
     * this error message when there are more than 10 in-flight requests.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_TOO_MANY_REQUESTS = 429,

    /**
     * @brief Shadow operation rejected: Internal service failure.
     *
     * Functions that may return this value:
     * - @ref shadow_function_timeddelete
     * - @ref shadow_function_timedget
     * - @ref shadow_function_timedupdate
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_SERVER_ERROR = 500,
} AwsIotShadowError_t;

/**
 * @ingroup shadow_datatypes_enums
 * @brief Types of Shadow library callbacks.
 *
 * One of these values will be placed in #AwsIotShadowCallbackParam_t.callbackType
 * to identify the reason for invoking a callback function.
 */
typedef enum AwsIotShadowCallbackType
{
    AWS_IOT_SHADOW_DELETE_COMPLETE, /**< Callback invoked because a [Shadow delete](@ref shadow_function_delete) completed. */
    AWS_IOT_SHADOW_GET_COMPLETE,    /**< Callback invoked because a [Shadow get](@ref shadow_function_get) completed. */
    AWS_IOT_SHADOW_UPDATE_COMPLETE, /**< Callback invoked because a [Shadow update](@ref shadow_function_update) completed. */
    AWS_IOT_SHADOW_DELTA_CALLBACK,  /**< Callback invoked for an incoming message on a [Shadow delta](@ref shadow_function_setdeltacallback) topic. */
    AWS_IOT_SHADOW_UPDATED_CALLBACK /**< Callback invoked for an incoming message on a [Shadow updated](@ref shadow_function_setupdatedcallback) topic. */
} AwsIotShadowCallbackType_t;

/*------------------------- Shadow parameter structs ------------------------*/

/**
 * @paramstructs{shadow,Shadow}
 */

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Parameter to a Shadow callback function.
 *
 * @paramfor Shadow callback functions
 *
 * The Shadow library passes this struct to a callback function whenever a
 * Shadow operation completes or a message is received on a Shadow delta or
 * updated topic.
 *
 * The valid members of this struct are different based on
 * #AwsIotShadowCallbackParam_t.callbackType. If the callback type is
 * #AWS_IOT_SHADOW_DELETE_COMPLETE, #AWS_IOT_SHADOW_GET_COMPLETE, or
 * #AWS_IOT_SHADOW_UPDATE_COMPLETE, then #AwsIotShadowCallbackParam_t.operation
 * is valid. Otherwise, if the callback type is #AWS_IOT_SHADOW_DELTA_CALLBACK
 * or #AWS_IOT_SHADOW_UPDATED_CALLBACK, then #AwsIotShadowCallbackParam_t.callback
 * is valid.
 *
 * @attention Any pointers in this callback parameter may be freed as soon as the
 * [callback function](@ref AwsIotShadowCallbackInfo_t.function) returns. Therefore,
 * data must be copied if it is needed after the callback function returns.
 * @attention The Shadow library may set strings that are not NULL-terminated.
 *
 * @see #AwsIotShadowCallbackInfo_t for the signature of a callback function.
 */
typedef struct AwsIotShadowCallbackParam
{
    AwsIotShadowCallbackType_t callbackType; /**< @brief Reason for invoking the Shadow callback function. */

    const char * pThingName;                 /**< @brief The Thing Name associated with this Shadow callback. */
    size_t thingNameLength;                  /**< @brief Length of #AwsIotShadowCallbackParam_t.pThingName. */

    union
    {
        /* Valid for completed Shadow operations. */
        struct
        {
            /* Valid for a completed Shadow GET operation. */
            struct
            {
                const char * pDocument;        /**< @brief Retrieved Shadow document. */
                size_t documentLength;         /**< @brief Length of retrieved Shadow document. */
            } get;                             /**< @brief Retrieved Shadow document, valid only for a completed [Shadow Get](@ref shadow_function_get). */

            AwsIotShadowError_t result;        /**< @brief Result of Shadow operation, e.g. succeeded or failed. */
            AwsIotShadowReference_t reference; /**< @brief Reference to the Shadow operation that completed. */
        } operation;                           /**< @brief Information on a completed Shadow operation. */

        /* Valid for a message on a Shadow delta or updated topic. */
        struct
        {
            const char * pDocument; /**< @brief Shadow delta or updated document. */
            size_t documentLength;  /**< @brief Length of Shadow delta or updated document. */
        } callback;                 /**< @brief Shadow document from an incoming delta or updated topic. */
    };
} AwsIotShadowCallbackParam_t;

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Information on a user-provided Shadow callback function.
 *
 * @paramfor @ref shadow_function_delete, @ref shadow_function_get, @ref
 * shadow_function_update, @ref shadow_function_setdeltacallback, @ref
 * shadow_function_setupdatedcallback
 *
 * Provides a function to be invoked when a Shadow operation completes or when a
 * Shadow document is received on a callback topic (delta or updated).
 *
 * @initializer{AwsIotShadowCallbackInfo_t,AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotShadowCallbackInfo
{
    void * param1; /**< @brief The first parameter to pass to the callback function. */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotShadowCallbackInfo_t.param1
     * @param[in] AwsIotShadowCallbackParam_t* Details on the outcome of the Shadow
     * operation or an incoming Shadow document.
     *
     * @see #AwsIotShadowCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         AwsIotShadowCallbackParam_t * const );
} AwsIotShadowCallbackInfo_t;

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Information on a Shadow document for @ref shadow_function_get or @ref
 * shadow_function_update.
 *
 * @paramfor @ref shadow_function_get, @ref shadow_function_update
 *
 * The valid members of this struct are different based on whether this struct
 * is passed to @ref shadow_function_get or @ref shadow_function_update. When
 * passed to @ref shadow_function_get, the `get` member is valid. When passed to
 * @ref shadow_function_update, the `update` member is valid. All other members
 * must always be set.
 *
 * @initializer{AwsIotShadowDocumentInfo_t,AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER}
 */
typedef struct AwsIotShadowDocumentInfo
{
    const char * pThingName; /**< @brief The Thing Name associated with this Shadow document. */
    size_t thingNameLength;  /**< @brief Length of #AwsIotShadowDocumentInfo_t.pThingName. */

    int QoS;                 /**< @brief QoS when sending a Shadow get or update message. See #AwsIotMqttPublishInfo_t.QoS. */
    int retryLimit;          /**< @brief Maximum number of retries for a Shadow get or update message. See #AwsIotMqttPublishInfo_t.retryLimit. */
    uint64_t retryMs;        /**< @brief First retry time for a Shadow get or update message. See #AwsIotMqttPublishInfo_t.retryMs. */

    union
    {
        /* Valid for Shadow get. */
        struct
        {
            /**
             * @brief Function to allocate memory for an incoming Shadow document.
             *
             * This only needs to be set if #AWS_IOT_SHADOW_FLAG_WAITABLE is passed to
             * @ref shadow_function_get.
             */
            void *( *mallocDocument )( size_t );
        } get; /**< @brief Valid members for @ref shadow_function_get. */

        /* Valid for Shadow update. */
        struct
        {
            const char * pUpdateDocument; /**< @brief The Shadow document to send in the update. */
            size_t updateDocumentLength;  /**< @brief Length of Shadow update document. */
        } update;                         /**< @brief Valid members for @ref shadow_function_update. */
    };
} AwsIotShadowDocumentInfo_t;

/*------------------------ Shadow defined constants -------------------------*/

/**
 * @constantspage{shadow,Shadow library}
 *
 * @section shadow_constants_initializers Shadow Initializers
 * @brief Provides default values for the data types of the Shadow library.
 *
 * @snippet this define_shadow_initializers
 *
 * All user-facing data types of the Shadow library should be initialized
 * using one of the following.
 *
 * @warning Failing to initialize a Shadow data type with the appropriate
 * initializer may result in undefined behavior!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 * AwsIotShadowCallbackInfo_t callbackInfo = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 * AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
 * AwsIotShadowReference_t reference = AWS_IOT_SHADOW_REFERENCE_INITIALIZER;
 * @endcode
 *
 * @section shadow_constants_flags Shadow Function Flags
 * @brief Flags that modify the behavior of Shadow library functions.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * Shadow library functions.
 *
 * The following flags are valid for the Shadow operation functions:
 * @ref shadow_function_delete, @ref shadow_function_get, @ref shadow_function_update,
 * and their <i>Timed</i> variants.
 * - #AWS_IOT_SHADOW_FLAG_WAITABLE <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_WAITABLE
 * - #AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS
 *
 * The following flags are valid for @ref shadow_function_removepersistentsubscriptions.
 * These flags are not valid for the Shadow operation functions.
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS
 *
 * @note The values of the flags may change at any time in future versions, but
 * their names will remain the same. Additionally, flags which may be used at
 * the same time will be bitwise-exclusive of each other.
 */

/* @[define_shadow_initializers] */
#define AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER           { 0 } /**< @brief Initializer for #AwsIotShadowCallbackInfo_t. */
#define AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER           { 0 } /**< @brief Initializer for #AwsIotShadowDocumentInfo_t. */
#define AWS_IOT_SHADOW_REFERENCE_INITIALIZER               NULL  /**< @brief Initializer for #AwsIotShadowReference_t. */
/* @[define_shadow_initializers] */

/**
 * @brief Allows the use of @ref shadow_function_wait for blocking until completion.
 *
 * This flag is only valid if passed to the functions @ref shadow_function_delete,
 * @ref shadow_function_get, or @ref shadow_function_update.
 *
 * An #AwsIotShadowReference_t <b>MUST</b> be provided if this flag is set.
 * Additionally, an #AwsIotShadowCallbackInfo_t <b>MUST NOT</b> be provided.
 *
 * @note If this flag is set, @ref shadow_function_wait <b>MUST</b> be called to
 * clean up resources.
 */
#define AWS_IOT_SHADOW_FLAG_WAITABLE                       ( 0x00000001 )

/**
 * @brief Maintain the subscriptions for the Shadow operation topics, even after
 * this function returns.
 */
#define AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS             ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Shadow delete operation.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS    ( 0x00000001 )

/**
 * @brief Remove the persistent subscriptions from a Shadow get operation.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS       ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Shadow update operation.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS    ( 0x00000004 )

/*------------------------ Shadow library functions -------------------------*/

/**
 * @functionspage{shadow,Shadow library}
 * - @functionname{shadow_function_init}
 * - @functionname{shadow_function_cleanup}
 * - @functionname{shadow_function_delete}
 * - @functionname{shadow_function_timeddelete}
 * - @functionname{shadow_function_get}
 * - @functionname{shadow_function_timedget}
 * - @functionname{shadow_function_update}
 * - @functionname{shadow_function_timedupdate}
 * - @functionname{shadow_function_wait}
 * - @functionname{shadow_function_setdeltacallback}
 * - @functionname{shadow_function_setupdatedcallback}
 * - @functionname{shadow_function_removepersistentsubscriptions}
 * - @functionname{shadow_function_strerror}
 */

/**
 * @functionpage{AwsIotShadow_Init,shadow,init}
 * @functionpage{AwsIotShadow_Cleanup,shadow,cleanup}
 * @functionpage{AwsIotShadow_Delete,shadow,delete}
 * @functionpage{AwsIotShadow_TimedDelete,shadow,timeddelete}
 * @functionpage{AwsIotShadow_Get,shadow,get}
 * @functionpage{AwsIotShadow_TimedGet,shadow,timedget}
 * @functionpage{AwsIotShadow_Update,shadow,update}
 * @functionpage{AwsIotShadow_TimedUpdate,shadow,timedupdate}
 * @functionpage{AwsIotShadow_Wait,shadow,wait}
 * @functionpage{AwsIotShadow_SetDeltaCallback,shadow,setdeltacallback}
 * @functionpage{AwsIotShadow_SetUpdatedCallback,shadow,setupdatedcallback}
 * @functionpage{AwsIotShadow_RemovePersistentSubscriptions,shadow,removepersistentsubscriptions}
 * @functionpage{AwsIotShadow_strerror,shadow,strerror}
 */

/**
 * @brief One-time initialization function for the Shadow library.
 *
 * This function performs internal setup of the Shadow library. <b>It must be
 * called once (and only once) before calling any other Shadow function.</b>
 * Calling this function more than once without first calling @ref
 * shadow_function_cleanup may result in a crash.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref shadow_function_cleanup
 */
/* @[declare_shadow_init] */
AwsIotShadowError_t AwsIotShadow_Init( uint64_t mqttTimeout );
/* @[declare_shadow_init] */

/**
 * @brief One-time deinitialization function for the Shadow library.
 *
 * This function frees resources taken in @ref shadow_function_init. It should
 * be called to clean up the Shadow library. After this function returns, @ref
 * shadow_function_init must be called again before calling any other Shadow
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref shadow_function_init
 */
/* @[declare_shadow_cleanup] */
void AwsIotShadow_Cleanup( void );
/* @[declare_shadow_cleanup] */

/**
 * @brief Delete a Thing Shadow and receive an asynchronous notification when
 * the Delete completes.
 */
/* @[declare_shadow_delete] */
AwsIotShadowError_t AwsIotShadow_Delete( AwsIotMqttConnection_t mqttConnection,
                                         const char * const pThingName,
                                         size_t thingNameLength,
                                         uint32_t flags,
                                         const AwsIotShadowCallbackInfo_t * const pCallbackInfo,
                                         AwsIotShadowReference_t * const pDeleteRef );
/* @[declare_shadow_delete] */

/**
 * @brief Delete a Thing Shadow with a timeout.
 */
/* @[declare_shadow_timeddelete] */
AwsIotShadowError_t AwsIotShadow_TimedDelete( AwsIotMqttConnection_t mqttConnection,
                                              const char * const pThingName,
                                              size_t thingNameLength,
                                              uint32_t flags,
                                              uint64_t timeoutMs );
/* @[declare_shadow_timeddelete] */

/**
 * @brief Retrieve a Thing Shadow and receive an asynchronous notification when
 * the Shadow document is received.
 */
/* @[declare_shadow_get] */
AwsIotShadowError_t AwsIotShadow_Get( AwsIotMqttConnection_t mqttConnection,
                                      const AwsIotShadowDocumentInfo_t * const pGetInfo,
                                      uint32_t flags,
                                      const AwsIotShadowCallbackInfo_t * const pCallbackInfo,
                                      AwsIotShadowReference_t * const pGetRef );
/* @[declare_shadow_get] */

/**
 * @brief Retrieve a Thing Shadow with a timeout.
 */
/* @[declare_shadow_timedget] */
AwsIotShadowError_t AwsIotShadow_TimedGet( AwsIotMqttConnection_t mqttConnection,
                                           const AwsIotShadowDocumentInfo_t * const pGetInfo,
                                           uint32_t flags,
                                           uint64_t timeoutMs,
                                           const char ** const pShadowDocument,
                                           size_t * const pShadowDocumentLength );
/* @[declare_shadow_timedget] */

/**
 * @brief Send a Thing Shadow update and receive an asynchronous notification when
 * the Shadow Update completes.
 */
/* @[declare_shadow_update] */
AwsIotShadowError_t AwsIotShadow_Update( AwsIotMqttConnection_t mqttConnection,
                                         const AwsIotShadowDocumentInfo_t * const pUpdateInfo,
                                         uint32_t flags,
                                         const AwsIotShadowCallbackInfo_t * const pCallbackInfo,
                                         AwsIotShadowReference_t * const pUpdateRef );
/* @[declare_shadow_update] */

/**
 * @brief Send a Thing Shadow update with a timeout.
 */
/* @[declare_shadow_timedupdate] */
AwsIotShadowError_t AwsIotShadow_TimedUpdate( AwsIotMqttConnection_t mqttConnection,
                                              const AwsIotShadowDocumentInfo_t * const pUpdateInfo,
                                              uint32_t flags,
                                              uint64_t timeoutMs );
/* @[declare_shadow_timedupdate] */

/**
 * @brief Wait for a Shadow operation to complete.
 */
/* @[declare_shadow_wait] */
AwsIotShadowError_t AwsIotShadow_Wait( AwsIotShadowReference_t reference,
                                       uint64_t timeoutMs,
                                       const char ** const pShadowDocument,
                                       size_t * const pShadowDocumentLength );
/* @[declare_shadow_wait] */

/**
 * @brief Set a callback to be invoked when the Thing Shadow "desired" and "reported"
 * states differ.
 */
/* @[declare_shadow_setdeltacallback] */
AwsIotShadowError_t AwsIotShadow_SetDeltaCallback( AwsIotMqttConnection_t mqttConnection,
                                                   const char * const pThingName,
                                                   size_t thingNameLength,
                                                   uint32_t flags,
                                                   const AwsIotShadowCallbackInfo_t * const pDeltaCallback );
/* @[declare_shadow_setdeltacallback] */

/**
 * @brief Set a callback to be invoked when a Thing Shadow changes.
 */
/* @[declare_shadow_setupdatedcallback] */
AwsIotShadowError_t AwsIotShadow_SetUpdatedCallback( AwsIotMqttConnection_t mqttConnection,
                                                     const char * const pThingName,
                                                     size_t thingNameLength,
                                                     uint32_t flags,
                                                     const AwsIotShadowCallbackInfo_t * const pUpdatedCallback );
/* @[declare_shadow_setupdatedcallback] */

/**
 * @brief Remove persistent Thing Shadow operation topic subscriptions.
 *
 * Not safe to call with any in-progress operation. Does not affect callbacks.
 */
/* @[declare_shadow_removepersistentsubscriptions] */
AwsIotShadowError_t AwsIotShadow_RemovePersistentSubscriptions( AwsIotMqttConnection_t mqttConnection,
                                                                const char * const pThingName,
                                                                size_t thingNameLength,
                                                                uint32_t flags );
/* @[declare_shadow_removepersistentsubscriptions] */

/*------------------------- Shadow helper functions -------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotShadowError_t.
 */
/* @[declare_shadow_strerror] */
const char * AwsIotShadow_strerror( AwsIotShadowError_t status );
/* @[declare_shadow_strerror] */

#endif /* ifndef _AWS_IOT_SHADOW_H_ */
