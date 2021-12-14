<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20" doxygen_gitid="f246dd2f1c58eea39ea3f50c108019e4d4137bd5">
  <compound kind="file">
    <name>fleet_provisioning.c</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/source/</path>
    <filename>fleet__provisioning_8c.html</filename>
    <includes id="fleet__provisioning_8h" name="fleet_provisioning.h" local="yes" imported="no">fleet_provisioning.h</includes>
    <member kind="enumeration">
      <type></type>
      <name>TopicSuffix_t</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a6a2ded2de0317d8b58b4c07265849e57</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>TopicFormatSuffix_t</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>ae2186c39e0a5e041e526a9780f99ecf8</anchor>
      <arglist></arglist>
    </member>
    <member kind="function" static="yes">
      <type>static uint16_t</type>
      <name>getRegisterThingTopicLength</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>aa6fa157e7ad05b7e88f9a2005c2feafa</anchor>
      <arglist>(uint16_t templateNameLength, FleetProvisioningFormat_t format, FleetProvisioningApiTopics_t topic)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>writeTopicFragmentAndAdvance</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>ab33a667c9fad5e6a83c62501ecc0e213</anchor>
      <arglist>(char **pBufferCursor, const char *fragment, uint16_t length)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningStatus_t</type>
      <name>GetRegisterThingTopicCheckParams</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>acad7d4436099adf6101337e4c88e6add</anchor>
      <arglist>(const char *pTopicBuffer, FleetProvisioningFormat_t format, FleetProvisioningApiTopics_t topic, const char *pTemplateName, uint16_t templateNameLength, const uint16_t *pOutLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static TopicSuffix_t</type>
      <name>parseTopicSuffix</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>ac112435952e534367f464b9a69b6d187</anchor>
      <arglist>(const char *pRemainingTopic, uint16_t remainingLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static TopicFormatSuffix_t</type>
      <name>parseTopicFormatSuffix</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a63371dbc329c50b4e4ac446a5ea13edf</anchor>
      <arglist>(const char *pRemainingTopic, uint16_t remainingLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningTopic_t</type>
      <name>parseCreateCertificateFromCsrTopic</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a20c63d00de68d74e339462991246b3c7</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningTopic_t</type>
      <name>parseCreateKeysAndCertificateTopic</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a32c47313070e2fe96c1cfa5cb76fea38</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningTopic_t</type>
      <name>parseRegisterThingTopic</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a6bf2715b8d1ea4c5f353e4f60637daf9</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningStatus_t</type>
      <name>consumeIfMatch</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>aa2c93e30aa4711070186c5873094a3b8</anchor>
      <arglist>(const char **pBufferCursor, uint16_t *pRemainingLength, const char *matchString, uint16_t matchLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static FleetProvisioningStatus_t</type>
      <name>consumeTemplateName</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>ac2d2ca3c59e6b1553cd9efad7b58ce84</anchor>
      <arglist>(const char **pTopicCursor, uint16_t *pRemainingLength)</arglist>
    </member>
    <member kind="function">
      <type>FleetProvisioningStatus_t</type>
      <name>FleetProvisioning_GetRegisterThingTopic</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a93e9b2b2b04dce2b44bdcc3b119e1e60</anchor>
      <arglist>(char *pTopicBuffer, uint16_t bufferLength, FleetProvisioningFormat_t format, FleetProvisioningApiTopics_t topic, const char *pTemplateName, uint16_t templateNameLength, uint16_t *pOutLength)</arglist>
    </member>
    <member kind="function">
      <type>FleetProvisioningStatus_t</type>
      <name>FleetProvisioning_MatchTopic</name>
      <anchorfile>fleet__provisioning_8c.html</anchorfile>
      <anchor>a91ea5642331970028458fd423bd1aef6</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength, FleetProvisioningTopic_t *pOutApi)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>fleet_provisioning.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>fleet__provisioning_8h.html</filename>
    <includes id="fleet__provisioning__config__defaults_8h" name="fleet_provisioning_config_defaults.h" local="yes" imported="no">fleet_provisioning_config_defaults.h</includes>
    <member kind="define">
      <type>#define</type>
      <name>FP_TEMPLATENAME_MAX_LENGTH</name>
      <anchorfile>group__fleet__provisioning__constants.html</anchorfile>
      <anchor>ga2f834c9e68a5e1c79b0fe41739fed8bf</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a0fd101f9e47024346df61fbd87579933</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a51d0565a92f4f313f94f859ab949d691</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>aa506056a43d69fd3576faf22022dcd0a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a6babd8028c581bc3bea41f42eb0a3179</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a80c140f2a4fc5199095913df27054ee6</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>ae4e048375a58ce5ac4cfe3c508fe4714</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>abb76a0053a4a45497cc490a666e7a73f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>abecf8a4991854af8aa18cb179da79def</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_CERT_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>ae6f6ceaf1622ab6e228e7dd3ecc4c5b2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a88f11a446ac4bffbb6cf332687383ed9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>ae0bd40110aca81af43b51f375343f2df</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_CERT_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a61a46171af832cdc6564dd8b5eac48ec</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a111d0369a1a06936970b24ae4d6c786b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a670ede490b47799cea0a25c5c5ab1c63</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a1f33394595595d0bd31722f0feb1643d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a6c9d59fe1dff3756dc90ca273d0afea9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a58aa93ce757457afef26d9a4fb51e201</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a01b33155b80b5c021625d9ebd89edadc</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a6d44b2b1bb7fbb1011c0daedbc68ad2c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a830aaf1802f9787885ed2b7b3f25a456</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_CREATE_KEYS_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a603b46408035bae37abf3707e4378bf8</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a8864bb80ef9819194c3d29943bc54139</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>af48296f2b11ac3fad24424618d06f356</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_CREATE_KEYS_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a901e4db86f6c8da5b28d2db83cb9a857</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a94e1ef034ee6dc4e44150075ffb45e4e</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>afa855acbf6c3eae7cc4fcaea1c426444</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a92e0202a7b3eb2c272b667d7968bd074</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_PUBLISH_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a1bedb071f8ab3de5e5848d94d5755de3</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_ACCEPTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>abb9d69b9392c286d41f8f7de913bd8e5</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_REJECTED_TOPIC</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a35e501225282c161a042c2ed18fed31c</anchor>
      <arglist>(templateName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a4ae2ec8e1bf87d1433957a56175bcac1</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>aa29a973f2428062822a5c74530b40111</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_JSON_REGISTER_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>aca74298be0fc14ba8ce6e72b24c72743</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_PUBLISH_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a69818e2dd6b048272a2da1572d4f50f5</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_ACCEPTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>abc533832a42f80deecce0488becb3113</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_CBOR_REGISTER_REJECTED_LENGTH</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>acee97aee30f3cf1ca47a02c3af18359f</anchor>
      <arglist>(templateNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_CSR_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a0ec4d434d439675a7d05655fd1e31c3b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_OWNERSHIP_TOKEN_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a25cd9d090a2fd2b6e36449fbd353813a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_CERTIFICATE_ID_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a4884e4ae91d9f87231dac4a35974582c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_CERTIFICATE_PEM_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a21d0c75023d9e949a1fa6ffb8658ee46</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_PRIVATE_KEY_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a2df4c29ee74189ea63e6c8fb12eaf77a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_PARAMETERS_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a9ff7a83e9a96467766ab761887c9ec68</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_DEVICE_CONFIG_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a168ea96f13021dfe88a09ca806c2d279</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_THING_NAME_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a4154fe2f688d33b3a2d419413d1e2bcb</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_STATUS_CODE_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>ad4ace466c7aaf42d7c88327f8b5e12e8</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_ERROR_CODE_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a0e322858d583a898018fb8b0a75b7fdd</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FP_API_ERROR_MESSAGE_KEY</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a473d9a0530a4586522095d4441b32602</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningStatus_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga8c5e9f177dd8c96b5b59308c02b695a4</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningTopic_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga4becd179796394efce032c76c3b68a97</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningApiTopics_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga7b8a658b4ff577b6bef3f91907462900</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningFormat_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>gae6845e3db56619e175c77d79c3fbadd2</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>FleetProvisioningStatus_t</type>
      <name>FleetProvisioning_GetRegisterThingTopic</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a93e9b2b2b04dce2b44bdcc3b119e1e60</anchor>
      <arglist>(char *pTopicBuffer, uint16_t bufferLength, FleetProvisioningFormat_t format, FleetProvisioningApiTopics_t topic, const char *pTemplateName, uint16_t templateNameLength, uint16_t *pOutLength)</arglist>
    </member>
    <member kind="function">
      <type>FleetProvisioningStatus_t</type>
      <name>FleetProvisioning_MatchTopic</name>
      <anchorfile>fleet__provisioning_8h.html</anchorfile>
      <anchor>a91ea5642331970028458fd423bd1aef6</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength, FleetProvisioningTopic_t *pOutApi)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>fleet_provisioning_config_defaults.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>fleet__provisioning__config__defaults_8h.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG</name>
      <anchorfile>fleet__provisioning__config__defaults_8h.html</anchorfile>
      <anchor>a169bfe3dbb9e304af9ebff9536107089</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogError</name>
      <anchorfile>fleet__provisioning__config__defaults_8h.html</anchorfile>
      <anchor>a8d9dbaaa88129137a4c68ba0456a18b1</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogWarn</name>
      <anchorfile>fleet__provisioning__config__defaults_8h.html</anchorfile>
      <anchor>a7da92048aaf0cbfcacde9539c98a0e05</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogInfo</name>
      <anchorfile>fleet__provisioning__config__defaults_8h.html</anchorfile>
      <anchor>a00810b1cb9d2f25d25ce2d4d93815fba</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogDebug</name>
      <anchorfile>fleet__provisioning__config__defaults_8h.html</anchorfile>
      <anchor>af60e8ffc327d136e5d0d8441ed98c98d</anchor>
      <arglist>(message)</arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>fleet_provisioning_enum_types</name>
    <title>Enumerated Types</title>
    <filename>group__fleet__provisioning__enum__types.html</filename>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningStatus_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga8c5e9f177dd8c96b5b59308c02b695a4</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningTopic_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga4becd179796394efce032c76c3b68a97</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningApiTopics_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>ga7b8a658b4ff577b6bef3f91907462900</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>FleetProvisioningFormat_t</name>
      <anchorfile>group__fleet__provisioning__enum__types.html</anchorfile>
      <anchor>gae6845e3db56619e175c77d79c3fbadd2</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>fleet_provisioning_constants</name>
    <title>Constants</title>
    <filename>group__fleet__provisioning__constants.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>FP_TEMPLATENAME_MAX_LENGTH</name>
      <anchorfile>group__fleet__provisioning__constants.html</anchorfile>
      <anchor>ga2f834c9e68a5e1c79b0fe41739fed8bf</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_design</name>
    <title>Design</title>
    <filename>fleet_provisioning_design.html</filename>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_config</name>
    <title>Configurations</title>
    <filename>fleet_provisioning_config.html</filename>
    <docanchor file="fleet_provisioning_config.html">FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG</docanchor>
    <docanchor file="fleet_provisioning_config.html" title="LogError">fleet_provisioning_logerror</docanchor>
    <docanchor file="fleet_provisioning_config.html" title="LogWarn">fleet_provisioning_logwarn</docanchor>
    <docanchor file="fleet_provisioning_config.html" title="LogInfo">fleet_provisioning_loginfo</docanchor>
    <docanchor file="fleet_provisioning_config.html" title="LogDebug">fleet_provisioning_logdebug</docanchor>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_functions</name>
    <title>Functions</title>
    <filename>fleet_provisioning_functions.html</filename>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_getregisterthingtopic_function</name>
    <title>FleetProvisioning_GetRegisterThingTopic</title>
    <filename>fleet_provisioning_getregisterthingtopic_function.html</filename>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_matchtopic_function</name>
    <title>FleetProvisioning_MatchTopic</title>
    <filename>fleet_provisioning_matchtopic_function.html</filename>
  </compound>
  <compound kind="page">
    <name>fleet_provisioning_porting</name>
    <title>Porting Guide</title>
    <filename>fleet_provisioning_porting.html</filename>
    <docanchor file="fleet_provisioning_porting.html" title="Configuration Macros">fleet_provisioning_porting_config</docanchor>
  </compound>
  <compound kind="page">
    <name>index</name>
    <title>Overview</title>
    <filename>index.html</filename>
    <docanchor file="index.html">fleet_provisioning</docanchor>
    <docanchor file="index.html" title="Memory Requirements">fleet_provisioning_memory_requirements</docanchor>
  </compound>
</tagfile>
