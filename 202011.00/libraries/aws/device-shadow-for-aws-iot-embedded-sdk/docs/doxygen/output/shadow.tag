<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20" doxygen_gitid="f246dd2f1c58eea39ea3f50c108019e4d4137bd5">
  <compound kind="file">
    <name>shadow.c</name>
    <path>C:/b/aws-iot-device-sdk-embedded-c-fork/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/source/</path>
    <filename>shadow_8c.html</filename>
    <includes id="shadow_8h" name="shadow.h" local="yes" imported="no">shadow.h</includes>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_ACCEPTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a3314f371c8b2ef0884e6508e3afdaf41</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_REJECTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a2691fddfde4eabf6421c4a6eb97ff11f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_DELTA</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>aab93fbc2127186ea1859254e3587c716</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_DOCUMENTS</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a14949898540fe2c8637dde7990043a21</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_ACCEPTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>ab9e1c6c82ed719cc442bdd5e44de9c10</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_REJECTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a6143bdaf412b551a03bf77d8d7a17dd3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_ACCEPTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a2f5623d61e9678b3ebd6f2264cb477c1</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_REJECTED</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a0ab1b932d1f053f46a2eb9d761efcb80</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_ACCEPTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a8f3d68afa47e544c0853d00c20a4318d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_REJECTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>af0dd9ca4f193c487d2b073616af49da1</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_DOCUMENTS_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a9b96e303bacfd5d61d1fb7ec7cb33573</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_DELTA_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>ae60e52c043a851b445e687aca9851fe9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_ACCEPTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a193688dfbfadcf4e62cedc1954e2f90a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_REJECTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a82f4f20e9a4637dcc8319cd58238c01f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_ACCEPTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a2bd6b1ba6013dbe3dce4dfafd416f6c3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_REJECTED_LENGTH</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a47d5acf6c9fec029e83d321c26653c65</anchor>
      <arglist></arglist>
    </member>
    <member kind="function" static="yes">
      <type>static ShadowStatus_t</type>
      <name>containsSubString</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>aad2a9736dcde952f1fc81a2f2dd9ef9c</anchor>
      <arglist>(const char *pString, uint16_t stringLength, const char *pSubString, uint16_t subStringLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static ShadowStatus_t</type>
      <name>validateThingName</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a453269f0c9e15fe4c8b940888752fe94</anchor>
      <arglist>(const char *pString, uint16_t stringLength, uint16_t *pThingNameLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static ShadowStatus_t</type>
      <name>extractShadowMessageType</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a44ac471c87ff242631452113f64db82b</anchor>
      <arglist>(const char *pString, uint16_t stringLength, ShadowMessageType_t *pMessageType)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static const char *</type>
      <name>getShadowOperationString</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a55cea962b2488282937660bf77e495be</anchor>
      <arglist>(ShadowTopicStringType_t topicType)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static uint16_t</type>
      <name>getShadowOperationLength</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a055099a3dec4d191e4e681483d0096f8</anchor>
      <arglist>(ShadowTopicStringType_t topicType)</arglist>
    </member>
    <member kind="function">
      <type>ShadowStatus_t</type>
      <name>Shadow_MatchTopic</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>a3ba8ea42875554cbec68d99178ef948c</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength, ShadowMessageType_t *pMessageType, const char **pThingName, uint16_t *pThingNameLength)</arglist>
    </member>
    <member kind="function">
      <type>ShadowStatus_t</type>
      <name>Shadow_GetTopicString</name>
      <anchorfile>shadow_8c.html</anchorfile>
      <anchor>ad42141061221798a5fe5a9efd9f1684f</anchor>
      <arglist>(ShadowTopicStringType_t topicType, const char *pThingName, uint8_t thingNameLength, char *pTopicBuffer, uint16_t bufferSize, uint16_t *pOutLength)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>shadow.h</name>
    <path>C:/b/aws-iot-device-sdk-embedded-c-fork/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>shadow_8h.html</filename>
    <includes id="shadow__config__defaults_8h" name="shadow_config_defaults.h" local="yes" imported="no">shadow_config_defaults.h</includes>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_PREFIX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga247201767a9d4e96e68659b3d45b56fa</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_PREFIX_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga59c22b8ca0015dbfc31e791d25a99e1c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gae632f7b67feb5e0523a2d417bc269808</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga587bbe5229d85b6080f2b0cc7fda193c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3ad1b29d634829613e9a9c15b32cdfca</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga95123f616be6c6daea8b87922e37f748</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga9af4141be718b1c3722c4b6af2a9e8d2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3aff5db93f1b232b414b01553dedbea4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_ACCEPTED</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga2555351e653e1db780c9868d1bb2b509</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_ACCEPTED_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3264059dc3013a79e18b67bc06d88f69</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_REJECTED</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga1a0642131b9a46928e52e77edd12d5d2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_REJECTED_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga77f4b26fbe2704fdd487176b2b264b9a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DELTA</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga240b2250a6d4c2ff22efd09f44467302</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DELTA_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gad7ff1f3d0c7c04350e0cab841583dd10</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DOCUMENTS</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gadbc41cdfbace3887ccae228abae2496a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DOCUMENTS_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga77996f84fbc11a25684f1efff4c5d39b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_NULL</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga8c4621347f122281206cc7e720e74862</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_NULL_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3ae17b88b5eaf29c2f7c351d64a43b5f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_THINGNAME_LENGTH_MAX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga869560502bc342389e18abb4a8dcc44c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gaf220bc585744d3226c370bf7d108be43</anchor>
      <arglist>(operationLength, suffixLength, thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_UPDATE</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a2d88d5b629b2949e5e88a4bb99b9824c</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a0f9cfc57b778ea1800b67936de7889d8</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_UPDATE_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>adca90dd211f1814c64b0f8e0e10c7518</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a1530af1581d500a8ad3a4a33e60db725</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_UPDATE_DELTA</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a2590f480f923d12cbf5d42d658f33907</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_GET</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>aaffe89fecaad4540e70d022474da112a</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_GET_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a82bd24b19dc44b91581925419e881b4c</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_GET_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a12a39264a971cb83266965abc7f4d2a1</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_DELETE</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a21c97aa81ad721f2b7296a7feca20c12</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a9b090af699bc85da71bbe2c9a8983fb0</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_DELETE_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a42e06e23712168c9d78d24c32b439b13</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_MAX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga68b2bddcf124940a061481c32218a600</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gaad6bc554cb9be80281457bfcaf0e9eea</anchor>
      <arglist>(thingName, operation, suffix)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_UPDATE</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a3b22295c60ac864ce115f9d9217f2ebb</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_UPDATE_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>ab71da3b18dfe48daf56257114868bd25</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_UPDATE_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a84c91c5635c869c96295cc880842bd44</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>ad61164381eb932aff862e9eb193d6b97</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_UPDATE_DELTA</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>af4c894d53a086e805c9202dc51393a5a</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_GET</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a2104c07f91b0ed6dbac9404c03ec2928</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_GET_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a002707cf823ffd3568138a1743956161</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_GET_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a042631b8ff0edcb69f9d7454f8b37ece</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_DELETE</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>aff9adba7f638da1983449b2f4106f584</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_DELETE_ACCEPTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>ab670e88ba87afb267d15dccce29602f6</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING_DELETE_REJECTED</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a9e0d8a4cef6d2795c3f96546180bb0a5</anchor>
      <arglist>(thingName)</arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>ShadowMessageType_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gac953015263099970421c6af6ce1ccba9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>ShadowTopicStringType_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>ga22d6eeafd1388d2392ef488d4281b813</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>ShadowStatus_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>ga41ed1ee9c48c83638bef476fd2773398</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_SUCCESS</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398a568e9c9ebfb0ae4d11587ea70694f855</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_FAIL</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ac012ee2b49d3335869e406c7fbaa81b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_BAD_PARAMETER</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398a0de4231574a9757a55db7de7adf36dcb</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_BUFFER_TOO_SMALL</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ab3f0d6b2e5376c60bab1fa000c0f6b3b</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_THINGNAME_PARSE_FAILED</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398afa6fde5609e538c824bdec4c4f2b5267</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_SHADOW_MESSAGE_TYPE_PARSE_FAILED</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ac506c88ce214603b51ba02f02ce4847c</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>ShadowStatus_t</type>
      <name>Shadow_GetTopicString</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>ad42141061221798a5fe5a9efd9f1684f</anchor>
      <arglist>(ShadowTopicStringType_t topicType, const char *pThingName, uint8_t thingNameLength, char *pTopicBuffer, uint16_t bufferSize, uint16_t *pOutLength)</arglist>
    </member>
    <member kind="function">
      <type>ShadowStatus_t</type>
      <name>Shadow_MatchTopic</name>
      <anchorfile>shadow_8h.html</anchorfile>
      <anchor>a3ba8ea42875554cbec68d99178ef948c</anchor>
      <arglist>(const char *pTopic, uint16_t topicLength, ShadowMessageType_t *pMessageType, const char **pThingName, uint16_t *pThingNameLength)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>shadow_config_defaults.h</name>
    <path>C:/b/aws-iot-device-sdk-embedded-c-fork/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>shadow__config__defaults_8h.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_DO_NOT_USE_CUSTOM_CONFIG</name>
      <anchorfile>shadow__config__defaults_8h.html</anchorfile>
      <anchor>a728b94a3302bb00789aba09241a0256f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogError</name>
      <anchorfile>shadow__config__defaults_8h.html</anchorfile>
      <anchor>a8d9dbaaa88129137a4c68ba0456a18b1</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogWarn</name>
      <anchorfile>shadow__config__defaults_8h.html</anchorfile>
      <anchor>a7da92048aaf0cbfcacde9539c98a0e05</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogInfo</name>
      <anchorfile>shadow__config__defaults_8h.html</anchorfile>
      <anchor>a00810b1cb9d2f25d25ce2d4d93815fba</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogDebug</name>
      <anchorfile>shadow__config__defaults_8h.html</anchorfile>
      <anchor>af60e8ffc327d136e5d0d8441ed98c98d</anchor>
      <arglist>(message)</arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>shadow_enum_types</name>
    <title>Enumerated Types</title>
    <filename>group__shadow__enum__types.html</filename>
    <member kind="enumeration">
      <type></type>
      <name>ShadowMessageType_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gac953015263099970421c6af6ce1ccba9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>ShadowTopicStringType_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>ga22d6eeafd1388d2392ef488d4281b813</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>ShadowStatus_t</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>ga41ed1ee9c48c83638bef476fd2773398</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_SUCCESS</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398a568e9c9ebfb0ae4d11587ea70694f855</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_FAIL</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ac012ee2b49d3335869e406c7fbaa81b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_BAD_PARAMETER</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398a0de4231574a9757a55db7de7adf36dcb</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_BUFFER_TOO_SMALL</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ab3f0d6b2e5376c60bab1fa000c0f6b3b</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_THINGNAME_PARSE_FAILED</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398afa6fde5609e538c824bdec4c4f2b5267</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SHADOW_SHADOW_MESSAGE_TYPE_PARSE_FAILED</name>
      <anchorfile>group__shadow__enum__types.html</anchorfile>
      <anchor>gga41ed1ee9c48c83638bef476fd2773398ac506c88ce214603b51ba02f02ce4847c</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>shadow_constants</name>
    <title>Constants</title>
    <filename>group__shadow__constants.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_PREFIX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga247201767a9d4e96e68659b3d45b56fa</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_PREFIX_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga59c22b8ca0015dbfc31e791d25a99e1c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gae632f7b67feb5e0523a2d417bc269808</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_DELETE_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga587bbe5229d85b6080f2b0cc7fda193c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3ad1b29d634829613e9a9c15b32cdfca</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_GET_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga95123f616be6c6daea8b87922e37f748</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga9af4141be718b1c3722c4b6af2a9e8d2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_OP_UPDATE_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3aff5db93f1b232b414b01553dedbea4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_ACCEPTED</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga2555351e653e1db780c9868d1bb2b509</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_ACCEPTED_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3264059dc3013a79e18b67bc06d88f69</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_REJECTED</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga1a0642131b9a46928e52e77edd12d5d2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_REJECTED_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga77f4b26fbe2704fdd487176b2b264b9a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DELTA</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga240b2250a6d4c2ff22efd09f44467302</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DELTA_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gad7ff1f3d0c7c04350e0cab841583dd10</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DOCUMENTS</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gadbc41cdfbace3887ccae228abae2496a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_DOCUMENTS_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga77996f84fbc11a25684f1efff4c5d39b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_NULL</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga8c4621347f122281206cc7e720e74862</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_SUFFIX_NULL_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga3ae17b88b5eaf29c2f7c351d64a43b5f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_THINGNAME_LENGTH_MAX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga869560502bc342389e18abb4a8dcc44c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gaf220bc585744d3226c370bf7d108be43</anchor>
      <arglist>(operationLength, suffixLength, thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_LENGTH_MAX</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>ga68b2bddcf124940a061481c32218a600</anchor>
      <arglist>(thingNameLength)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SHADOW_TOPIC_STRING</name>
      <anchorfile>group__shadow__constants.html</anchorfile>
      <anchor>gaad6bc554cb9be80281457bfcaf0e9eea</anchor>
      <arglist>(thingName, operation, suffix)</arglist>
    </member>
  </compound>
  <compound kind="page">
    <name>shadow_design</name>
    <title>Design</title>
    <filename>shadow_design.html</filename>
  </compound>
  <compound kind="page">
    <name>shadow_config</name>
    <title>Configurations</title>
    <filename>shadow_config.html</filename>
    <docanchor file="shadow_config.html">SHADOW_DO_NOT_USE_CUSTOM_CONFIG</docanchor>
    <docanchor file="shadow_config.html" title="LogError">shadow_logerror</docanchor>
    <docanchor file="shadow_config.html" title="LogWarn">shadow_logwarn</docanchor>
    <docanchor file="shadow_config.html" title="LogInfo">shadow_loginfo</docanchor>
    <docanchor file="shadow_config.html" title="LogDebug">shadow_logdebug</docanchor>
  </compound>
  <compound kind="page">
    <name>shadow_functions</name>
    <title>Functions</title>
    <filename>shadow_functions.html</filename>
  </compound>
  <compound kind="page">
    <name>shadow_matchtopic_function</name>
    <title>Shadow_MatchTopic</title>
    <filename>shadow_matchtopic_function.html</filename>
  </compound>
  <compound kind="page">
    <name>shadow_gettopicstring_function</name>
    <title>Shadow_GetTopicString</title>
    <filename>shadow_gettopicstring_function.html</filename>
  </compound>
  <compound kind="page">
    <name>shadow_porting</name>
    <title>Porting Guide</title>
    <filename>shadow_porting.html</filename>
    <docanchor file="shadow_porting.html" title="Configuration Macros">shadow_porting_config</docanchor>
  </compound>
  <compound kind="page">
    <name>index</name>
    <title>Overview</title>
    <filename>index.html</filename>
    <docanchor file="index.html">shadow</docanchor>
    <docanchor file="index.html" title="Memory Requirements">shadow_memory_requirements</docanchor>
  </compound>
</tagfile>
