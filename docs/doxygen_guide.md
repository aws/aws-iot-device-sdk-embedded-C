# Creating Doxygen documentation for a new library
1. All supporting files were created with Doxygen version 1.9.2. Please download
from https://sourceforge.net/projects/doxygen/files/rel-1.9.2/.

1. Your library API should have each function, data type, and constant documented
according to the Doxygen format using **@brief** and **@param**. Doxygen will output
warnings if you are missing this. Please see the MQTT library for example documentation.
    An example function:
    ```C
    /**
     * @brief Function description.
     *
     * @param[in] input An input parameter.
     * @param[out] output An output parameter.
     *
     * @return List of values returned.
     *
     * <b>Example</b>
     * @code{c}
     * status = MyFunction(input, output);
     * @endcode
     */
    /* @[declare_mylibrary_myfunction] */
    size_t MyLibrary_MyFunction( size_t input, size_t * output );
    /* @[declare_mylibrary_myfunction] */
    ```

1. Your library must have a **@file** command and **@brief** description in each
file for Doxygen to know to parse the file as part of the library. Please see the
MQTT library for examples.
    An example from mqtt.h:
    ```C
    /**
     * @file mqtt.h
     * @brief User-facing functions of the MQTT 3.1.1 library.
     */
    ```

1. Please associate each data type and constant in your library's public API to
a group so that it will appear in the custom Doxygen pages.
    For each comment block add the following commands to associate your data types and constants:

    | Data Type | Command |
    | ---       | ---     |
    | constant | **@ingroup** <library_name>_constants |
    | function pointer | **@ingroup** <library_name>_callback_types |
    | enum | **@ingroup** <library_name>_enum_types |
    | struct | **@ingroup** <library_name>_struct_types |


    Some examples of grouped data types and constants in mqtt.h:
    ```C
    /**
     * @ingroup mqtt_constants
     * @brief Invalid packet identifier.
     *
     * Zero is an invalid packet identifier as per MQTT v3.1.1 spec.
     */
    #define MQTT_PACKET_ID_INVALID    ( ( uint16_t ) 0U )

    /**
     * @ingroup mqtt_callback_types
     * @brief Application provided callback to retrieve the current time in
     * milliseconds.
     *
     * @return The current time in milliseconds.
     */
    typedef uint32_t (* MQTTGetCurrentTimeFunc_t )( void );

    /**
     * @ingroup mqtt_enum_types
     * @brief Values indicating if an MQTT connection exists.
     */
    typedef enum MQTTConnectionStatus
    {
        MQTTNotConnected, /**< @brief MQTT Connection is inactive. */
        MQTTConnected     /**< @brief MQTT Connection is active. */
    } MQTTConnectionStatus_t;

    /**
     * @ingroup mqtt_struct_types
     * @brief An element of the state engine records for QoS 1 or Qos 2 publishes.
     */
    typedef struct MQTTPubAckInfo
    {
        uint16_t packetId;               /**< @brief The packet ID of the original PUBLISH. */
        MQTTQoS_t qos;                   /**< @brief The QoS of the original PUBLISH. */
        MQTTPublishState_t publishState; /**< @brief The current state of the publish process. */
    } MQTTPubAckInfo_t;
    ```

1. Please add **/\* \@\[declare_\<function name\>\] \*/** around each API function
so that Doxygen can copy the function signature to custom function pages.

    ```C
    /* @[declare_mylibrary_myfunction] */
    size_t MyLibrary_MyFunction( size_t input, size_t * output );
    /* @[declare_mylibrary_myfunction] */
    ```

1. Please copy the all of the template pages to your library's docs/doxygen folder.
For our CI to detect files correctly, please keep the folder name as *docs/doxygen*
and all of the files names the same.

    ```console
    cp -R <csdk_root>/docs/doxygen_templates <library_root>/docs/doxygen
    ```

1. Search for "FIXME"s in <library_root>/docs/doxygen/config.doxygen and update with
your library information.

1. Search for "FIXME"s in <library_root>/docs/doxygen/pages.txt and update with your
library's information.

1. Add your library to the CSDK's list of libraries, in the first section in <csdk_root>/docs/doxygen/pages.txt.

    ```doxygen
    - [<library_name>](@ref library_name) - [<library_repo_name>](<library_repo_github_url>)
    ```

1. Add the name of your library's Doxygen TAG file to the list of library tag files in <csdk_root>/docs/doxygen/config.doxyfile configuration option named `TAGFILES`:

    ```doxygen
    TAGFILES               = <csdk_path_to_library>/docs/doxygen/output/<library_name>.tag=../../../../<csdk_path_to_library>/docs/doxygen/output/html
    ```

1. Generate Doxygen with the current working directory as the root of your library's repo:

    ```console
    doxygen docs/doxygen/config.doxygen
    ```

    Fix all warnings.

1. Generate Doxygen in the CSDK repo root:

    ```console
    git submodule update --init --checkout
    python tools/doxygen/generate_docs.py --root .
    ```

    Fix all warnings.
