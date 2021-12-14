<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20" doxygen_gitid="f246dd2f1c58eea39ea3f50c108019e4d4137bd5">
  <compound kind="file">
    <name>sigv4.c</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/</path>
    <filename>sigv4_8c.html</filename>
    <includes id="sigv4_8h" name="sigv4.h" local="yes" imported="no">sigv4.h</includes>
    <includes id="sigv4__internal_8h" name="sigv4_internal.h" local="yes" imported="no">sigv4_internal.h</includes>
    <includes id="sigv4__quicksort_8h" name="sigv4_quicksort.h" local="yes" imported="no">sigv4_quicksort.h</includes>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>intToAscii</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ae42595f858beec39a765755e277460a8</anchor>
      <arglist>(int32_t value, char **pBuffer, size_t bufferLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>generateCanonicalAndSignedHeaders</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>acc95a36d5ca043076852fd090405f873</anchor>
      <arglist>(const char *pHeaders, size_t headersLen, uint32_t flags, CanonicalContext_t *canonicalRequest, char **pSignedHeaders, size_t *pSignedHeadersLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>appendSignedHeaders</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ae1578b175aaaa9849a5e0d63a71d25ec</anchor>
      <arglist>(size_t headerCount, uint32_t flags, CanonicalContext_t *canonicalRequest, char **pSignedHeaders, size_t *pSignedHeadersLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>appendCanonicalizedHeaders</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ab6b5d3b71936542c8bb0322c32991d55</anchor>
      <arglist>(size_t headerCount, uint32_t flags, CanonicalContext_t *canonicalRequest)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>parseHeaderKeyValueEntries</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a641788264214495655fc9905a2e22841</anchor>
      <arglist>(const char *pHeaders, size_t headersDataLen, uint32_t flags, size_t *headerCount, CanonicalContext_t *canonicalRequest)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>copyHeaderStringToCanonicalBuffer</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a257f2337a87f1eee1358b2dcaf150bdd</anchor>
      <arglist>(const char *pData, size_t dataLen, uint32_t flags, char separator, CanonicalContext_t *canonicalRequest)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static bool</type>
      <name>isTrimmableSpace</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a1c55af8f76e7fd110ce75c5c7691339c</anchor>
      <arglist>(const char *value, size_t index, size_t valLen, size_t trimmedLength)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>generateCanonicalRequestUntilHeaders</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ab11d2468a4cc3ee277a136b3c320ed82</anchor>
      <arglist>(const SigV4Parameters_t *pParams, CanonicalContext_t *pCanonicalContext, char **pSignedHeaders, size_t *pSignedHeadersLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>generateAuthorizationValuePrefix</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a9f32917686451e1952717e8a68f999a3</anchor>
      <arglist>(const SigV4Parameters_t *pParams, const char *pAlgorithm, size_t algorithmLen, const char *pSignedHeaders, size_t signedHeadersLen, char *pAuthBuf, size_t *pAuthPrefixLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>writeLineToCanonicalRequest</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ab32ac5704f6143868e326b71ea0181d2</anchor>
      <arglist>(const char *pLine, size_t lineLen, CanonicalContext_t *pCanonicalContext)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>setQueryParameterKey</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a3e7468042ccd03c8686bfe4195441d1a</anchor>
      <arglist>(size_t currentParameter, const char *pKey, size_t keyLen, CanonicalContext_t *pCanonicalRequest)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>setQueryParameterValue</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>abcc91f0d413ad759a0cebbfef3f43a5d</anchor>
      <arglist>(size_t currentParameter, const char *pValue, size_t valueLen, CanonicalContext_t *pCanonicalRequest)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static int32_t</type>
      <name>hmacAddKey</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ae9366fa6817cf38befefe225a3d346f0</anchor>
      <arglist>(HmacContext_t *pHmacContext, const char *pKey, size_t keyLen, bool isKeyPrefix)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static int32_t</type>
      <name>hmacIntermediate</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a91e0b178798f5ff4e3e88d8dc41f66aa</anchor>
      <arglist>(HmacContext_t *pHmacContext, const char *pData, size_t dataLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static int32_t</type>
      <name>hmacFinal</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ab773cbedb30027889d6c3fd752c128f8</anchor>
      <arglist>(HmacContext_t *pHmacContext, char *pMac, size_t macLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static int32_t</type>
      <name>completeHmac</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>aa3c20454de317a6f7460d2cf0498c132</anchor>
      <arglist>(HmacContext_t *pHmacContext, const char *pKey, size_t keyLen, const char *pData, size_t dataLen, char *pOutput, size_t outputLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static int32_t</type>
      <name>completeHash</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a8528d08d3a3f4ce953ac0a18c5c4b7f9</anchor>
      <arglist>(const uint8_t *pInput, size_t inputLen, uint8_t *pOutput, size_t outputLen, const SigV4CryptoInterface_t *pCryptoInterface)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>completeHashAndHexEncode</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a76c455d7bda8ed3d4816c0ec0b546709</anchor>
      <arglist>(const char *pInput, size_t inputLen, char *pOutput, size_t *pOutputLen, const SigV4CryptoInterface_t *pCryptoInterface)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static size_t</type>
      <name>writeStringToSignPrefix</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a6a982381960ca00aa2ce9055b2a24273</anchor>
      <arglist>(char *pBufStart, const char *pAlgorithm, size_t algorithmLen, const char *pDateIso8601)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>writeStringToSign</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ac342ebde5d8f50559423b9eee8e5d84e</anchor>
      <arglist>(const SigV4Parameters_t *pParams, const char *pAlgorithm, size_t algorithmLen, CanonicalContext_t *pCanonicalContext)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>generateSigningKey</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a5fb52f313d91e0f65f36254e2505f240</anchor>
      <arglist>(const SigV4Parameters_t *pSigV4Params, HmacContext_t *pHmacContext, SigV4String_t *pSigningKey, size_t *pBytesRemaining)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>generateCredentialScope</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a44d258c14616fee40aae061a30bb825c</anchor>
      <arglist>(const SigV4Parameters_t *pSigV4Params, SigV4String_t *pCredScope)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>checkLeap</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a6675e05cc6d07aac4d6faa915e132230</anchor>
      <arglist>(const SigV4DateTime_t *pDateElements)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>validateDateTime</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ad1d4b13610004d066894740c47e24db2</anchor>
      <arglist>(const SigV4DateTime_t *pDateElements)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>addToDate</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ab755ba4a4993e1b666ab9070c3b1be98</anchor>
      <arglist>(const char formatChar, int32_t result, SigV4DateTime_t *pDateElements)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>scanValue</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ad1507dcc4a986cbb357cead564aec240</anchor>
      <arglist>(const char *pDate, const char formatChar, size_t readLoc, size_t lenToRead, SigV4DateTime_t *pDateElements)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>parseDate</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a826912da42f263c8bb18f498d7d1ab9b</anchor>
      <arglist>(const char *pDate, size_t dateLen, const char *pFormat, size_t formatLen, SigV4DateTime_t *pDateElements)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>verifyParamsToGenerateAuthHeaderApi</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a72386c1bb95ff33f62bfaf5c00596026</anchor>
      <arglist>(const SigV4Parameters_t *pParams, const char *pAuthBuf, const size_t *authBufLen, char *const *pSignature, const size_t *signatureLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>assignDefaultArguments</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a0a1d1591d06b22fae9906c16d38f0025</anchor>
      <arglist>(const SigV4Parameters_t *pParams, const char **pAlgorithm, size_t *algorithmLen)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static SigV4Status_t</type>
      <name>lowercaseHexEncode</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a67eb1d997c55d861014e7e0ba860b4ec</anchor>
      <arglist>(const SigV4String_t *pInputStr, SigV4String_t *pHexOutput)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static size_t</type>
      <name>sizeNeededForCredentialScope</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a5191c6d026491e2d204323723d2dd47b</anchor>
      <arglist>(const SigV4Parameters_t *pSigV4Params)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static size_t</type>
      <name>copyString</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ac7d33915690b63b45059c39e14f67bf0</anchor>
      <arglist>(char *destination, const char *source, size_t length)</arglist>
    </member>
    <member kind="function">
      <type>SigV4Status_t</type>
      <name>SigV4_AwsIotDateToIso8601</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>ac6f3d9773a15116d43b050ab09456c20</anchor>
      <arglist>(const char *pDate, size_t dateLen, char *pDateISO8601, size_t dateISO8601Len)</arglist>
    </member>
    <member kind="function">
      <type>SigV4Status_t</type>
      <name>SigV4_GenerateHTTPAuthorization</name>
      <anchorfile>sigv4_8c.html</anchorfile>
      <anchor>a46ab0bb656d9b24e3efdcf85c0b8a385</anchor>
      <arglist>(const SigV4Parameters_t *pParams, char *pAuthBuf, size_t *authBufLen, char **pSignature, size_t *signatureLen)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>sigv4.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>sigv4_8h.html</filename>
    <includes id="sigv4__config__defaults_8h" name="sigv4_config_defaults.h" local="yes" imported="no">sigv4_config_defaults.h</includes>
    <class kind="struct">SigV4CryptoInterface_t</class>
    <class kind="struct">SigV4HttpParameters_t</class>
    <class kind="struct">SigV4Credentials_t</class>
    <class kind="struct">SigV4Parameters_t</class>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_AWS4_HMAC_SHA256</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaab763fe2fe7acc18bb492c254d762ae3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_AWS4_HMAC_SHA256_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa9e9d97756a1f6389f6da8617170f08c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_DATE_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga0b4b6958b256d0a29275d34e9617c5f4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_SECURITY_TOKEN_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga3c7e4fecb06d49179202bc08b41b82d3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_STREAMING_AWS4_HMAC_SHA256_PAYLOAD</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga954dd406cb66a2d9140b1e4893d559e2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_CONTENT_SHA256_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaef74844bfe1983b6b84bf18b01cd4c4a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_STORAGE_CLASS_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gae3ebc0dbf384ba019f1cd16abd5c7fd6</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_ACCESS_KEY_ID_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gae09d1c889461e9bd3394e5fd41184432</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_SECRET_ACCESS_KEY_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga540d0660078b1f4b7a4ba1b46b3c96ad</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_ISO_STRING_LEN</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa96f2b005c358892fc9ae3f1ecc7f757</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_EXPECTED_LEN_RFC_3339</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga5fa31664388d3b37d415c31cfd0674f9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_EXPECTED_LEN_RFC_5322</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa07110bba8f36cd9e013e33d0f887155</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_PATH_IS_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga65f1081bc8e969ce7bc726d5bc1c5f7b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_QUERY_IS_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga16fa9ad1cc53594a061985c243c520b9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga9e9136345f456eb4c76bca582a88331f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_ALL_ARE_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga00b06a304245f49ac6084734046a3cfb</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>SigV4Status_t</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>ga9473b37a4c9e1e9b1d45d90b062d8df9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4Success</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a238f75db46434dcb1fa3e8bbdf048627</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InvalidParameter</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9aca7601341caf16c3fb93a0927b9f6ab6</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InsufficientMemory</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a2bb0cb0ecb7f2856a93b9c533d780e7c</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4ISOFormattingError</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a70fb09164f149921dbdabca0909aee1a</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4MaxHeaderPairCountExceeded</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a7201ec16e087837e7e405ae908014479</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4MaxQueryPairCountExceeded</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a717bf762306a480d172b76912f525478</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4HashError</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a682f99d6afd965cf64411eafc4985de9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InvalidHttpHeaders</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9aa535c1f048c34142ee558517b14d6d69</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>SigV4Status_t</type>
      <name>SigV4_GenerateHTTPAuthorization</name>
      <anchorfile>sigv4_8h.html</anchorfile>
      <anchor>a46ab0bb656d9b24e3efdcf85c0b8a385</anchor>
      <arglist>(const SigV4Parameters_t *pParams, char *pAuthBuf, size_t *authBufLen, char **pSignature, size_t *signatureLen)</arglist>
    </member>
    <member kind="function">
      <type>SigV4Status_t</type>
      <name>SigV4_AwsIotDateToIso8601</name>
      <anchorfile>sigv4_8h.html</anchorfile>
      <anchor>ac6f3d9773a15116d43b050ab09456c20</anchor>
      <arglist>(const char *pDate, size_t dateLen, char *pDateISO8601, size_t dateISO8601Len)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>sigv4_config_defaults.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>sigv4__config__defaults_8h.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_DO_NOT_USE_CUSTOM_CONFIG</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a0ab1431396b0b913ff80c322db7f6940</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_PROCESSING_BUFFER_LENGTH</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a9353c74dddc3c9a029a7c751c829360e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_MAX_HTTP_HEADER_COUNT</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>ad17cc8acc13555f0f342e044c56aec24</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_MAX_QUERY_PAIR_COUNT</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a2bfd94e48f0f5c010efc93e543cb946c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_WORST_CASE_SORT_STACK_SIZE</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>aa3c3aede260e152731bb9205bb16ca59</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HASH_MAX_BLOCK_LENGTH</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>af05827d843975b33de18e6926726fd82</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HASH_MAX_DIGEST_LENGTH</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>aa6e17a4868d62a37aac0d189f0035d69</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_USE_CANONICAL_SUPPORT</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a5433d84d55183ce4f86947815a213b3e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogError</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a8d9dbaaa88129137a4c68ba0456a18b1</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogWarn</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a7da92048aaf0cbfcacde9539c98a0e05</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogInfo</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>a00810b1cb9d2f25d25ce2d4d93815fba</anchor>
      <arglist>(message)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LogDebug</name>
      <anchorfile>sigv4__config__defaults_8h.html</anchorfile>
      <anchor>af60e8ffc327d136e5d0d8441ed98c98d</anchor>
      <arglist>(message)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>sigv4_internal.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>sigv4__internal_8h.html</filename>
    <includes id="sigv4__config__defaults_8h" name="sigv4_config_defaults.h" local="yes" imported="no">sigv4_config_defaults.h</includes>
    <class kind="struct">SigV4DateTime_t</class>
    <class kind="struct">SigV4String_t</class>
    <class kind="struct">SigV4ConstString_t</class>
    <class kind="struct">SigV4KeyValuePair_t</class>
    <class kind="struct">CanonicalContext_t</class>
    <class kind="struct">HmacContext_t</class>
    <member kind="define">
      <type>#define</type>
      <name>YEAR_MIN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a5ae56cfcc277b5ca9616640e51fa916e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>MONTH_ASCII_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a607705ef63831b55249bd52f4640f54b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>MONTH_NAMES</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ab2e9672209a299c7f71d989c90b41016</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>MONTH_DAYS</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>aa59bca774312f323b3923cf93e76a0b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FORMAT_RFC_3339</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ad42831e136dd13291631583a2f05695b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FORMAT_RFC_3339_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>aaf38dc0512d5e6f0ec4203331183753b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FORMAT_RFC_5322</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a56d79c844d441053cdcd3fb8bf92d41b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FORMAT_RFC_5322_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a28215d8bf739b003ed987fe1088c8827</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>ISO_YEAR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a56e53e4a004947001e38f049b6182656</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>ISO_NON_YEAR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a7ef889daf661f213345c765e19b3b9a5</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>ISO_DATE_SCOPE_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ad6dd66e1acaff9b62be78022aa2acd85</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CREDENTIAL_SCOPE_SEPARATOR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a3744aade0231260b8a129fe911085235</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CREDENTIAL_SCOPE_SEPARATOR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a9c54ab62deaec7b0eca7e32c2d557269</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CREDENTIAL_SCOPE_TERMINATOR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>aaff762da5baa81cad938cdb636373325</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CREDENTIAL_SCOPE_TERMINATOR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a3ab33c321a596ff5a72b164d3af06a72</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HTTP_EMPTY_PATH</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>af2bb2317c7f90b7db70b8f0150bb28fe</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HTTP_EMPTY_PATH_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a4842e1e66dec35cb8d5ad140db33be9e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>URI_ENCODED_SPECIAL_CHAR_SIZE</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a51dda8485aa25442633af06df0ede3d7</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>URI_DOUBLE_ENCODED_EQUALS_CHAR_SIZE</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>af3a9ab06317ce6ea90f416247d5a3db9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LINEFEED_CHAR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>af7588029cfe503a854f4956ca16e74ca</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LINEFEED_CHAR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a4755d6996781ffe101ef5adb4ce8b8eb</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HTTP_REQUEST_LINE_ENDING</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a524de65082b0444b0d5abc0ec3d55b4f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HTTP_REQUEST_LINE_ENDING_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a475afd1f322d8c81746800ad3485b579</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SPACE_CHAR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>af05fbe3f7666f4c5e2131431cb62a6be</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SPACE_CHAR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a61faf202870c1ba7c7ef675761ecc2af</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>S3_SERVICE_NAME</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a81d8855f91e03d3a7e5d5e4c670be1c9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>S3_SERVICE_NAME_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a1f2122709e77f0c46f2c67de1a029ac6</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HMAC_SIGNING_KEY_PREFIX</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ae849fc59c1be7f9be9d17a2812ade542</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HMAC_SIGNING_KEY_PREFIX_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ab1312b5568f580523d5aa8658b2beeb7</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_CREDENTIAL_PREFIX</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a3e1694e506c8c3fe0ed9295a92436a27</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_CREDENTIAL_PREFIX_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a19a640318e80312185eb887e789155d5</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SEPARATOR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a3db98e01e294085cdee3a37132e8b84e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SEPARATOR_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a1d7988aa48ab07f18dc4c20cf6cb5323</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SIGNED_HEADERS_PREFIX</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>aa08bf3ffa6d48a61470aaa87eb5d22af</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SIGNED_HEADERS_PREFIX_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ab222063448e05f4a5bfe2bc6928b1a3d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SIGNATURE_PREFIX</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>aa6382b82c885ff1b6bd98aa47e3108ac</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>AUTH_SIGNATURE_PREFIX_LEN</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a8c19a4e55d09df865b6ee5c62d591c03</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HMAC_INNER_PAD_BYTE</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a0aa1befec25d140bb9611f1aeb51897e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>HMAC_OUTER_PAD_BYTE</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a1cd37fb77466a9a7b8308d565d5f6370</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>LOG_INSUFFICIENT_MEMORY_ERROR</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a6f0551ef3b5510cc573a64f7e7c00d71</anchor>
      <arglist>(purposeOfWrite, bytesExceeded)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>FLAG_IS_SET</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>a44848f7b5aaba36a6b26dda7e1f3c4e5</anchor>
      <arglist>(bits, flag)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>isWhitespace</name>
      <anchorfile>sigv4__internal_8h.html</anchorfile>
      <anchor>ac975112ba9f532db68e2b1b3aa2efa89</anchor>
      <arglist>(c)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>sigv4_quicksort.c</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/</path>
    <filename>sigv4__quicksort_8c.html</filename>
    <includes id="sigv4__quicksort_8h" name="sigv4_quicksort.h" local="yes" imported="no">sigv4_quicksort.h</includes>
    <member kind="define">
      <type>#define</type>
      <name>PUSH_STACK</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>a00fec42cc605f715c158d2410752b10d</anchor>
      <arglist>(valueToPush, stack, index)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>POP_STACK</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>a20ab4ff852dbd6fdbab9bf8f43b55a2d</anchor>
      <arglist>(valueToPop, stack, index)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>swap</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>a70eb2bf43f1d7a0ba56db235adc2b3e6</anchor>
      <arglist>(void *pFirstItem, void *pSecondItem, size_t itemSize)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>quickSortHelper</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>a1dd36cccc6bf56f6f7c170d849d3f6f3</anchor>
      <arglist>(void *pArray, size_t low, size_t high, size_t itemSize, ComparisonFunc_t comparator)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static size_t</type>
      <name>partition</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>a76d2e6b0707a253ba641e9de589985ee</anchor>
      <arglist>(void *pArray, size_t low, size_t high, size_t itemSize, ComparisonFunc_t comparator)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>quickSort</name>
      <anchorfile>sigv4__quicksort_8c.html</anchorfile>
      <anchor>acc51ad5abb998f0756bb1501198a1273</anchor>
      <arglist>(void *pArray, size_t numItems, size_t itemSize, ComparisonFunc_t comparator)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>sigv4_quicksort.h</name>
    <path>/home/runner/work/aws-iot-device-sdk-embedded-C/aws-iot-device-sdk-embedded-C/libraries/aws/sigv4-for-aws-iot-embedded-sdk/source/include/</path>
    <filename>sigv4__quicksort_8h.html</filename>
    <includes id="sigv4__config__defaults_8h" name="sigv4_config_defaults.h" local="yes" imported="no">sigv4_config_defaults.h</includes>
    <member kind="typedef">
      <type>int32_t(*</type>
      <name>ComparisonFunc_t</name>
      <anchorfile>sigv4__quicksort_8h.html</anchorfile>
      <anchor>a27ae7db2dcd45e18aedaf77a191a6b3c</anchor>
      <arglist>)(const void *pFirstVal, const void *pSecondVal)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>quickSort</name>
      <anchorfile>sigv4__quicksort_8h.html</anchorfile>
      <anchor>acc51ad5abb998f0756bb1501198a1273</anchor>
      <arglist>(void *pArray, size_t numItems, size_t itemSize, ComparisonFunc_t comparator)</arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>CanonicalContext_t</name>
    <filename>struct_canonical_context__t.html</filename>
    <member kind="variable">
      <type>SigV4KeyValuePair_t</type>
      <name>pQueryLoc</name>
      <anchorfile>struct_canonical_context__t.html</anchorfile>
      <anchor>a51407763138a5c639412a324c4c2eafe</anchor>
      <arglist>[SIGV4_MAX_QUERY_PAIR_COUNT]</arglist>
    </member>
    <member kind="variable">
      <type>SigV4KeyValuePair_t</type>
      <name>pHeadersLoc</name>
      <anchorfile>struct_canonical_context__t.html</anchorfile>
      <anchor>a982200d406428b20b96ab3ce4427ebb1</anchor>
      <arglist>[SIGV4_MAX_HTTP_HEADER_COUNT]</arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>pBufProcessing</name>
      <anchorfile>struct_canonical_context__t.html</anchorfile>
      <anchor>a7b4aa5a82504acd7701aa9513a2a5871</anchor>
      <arglist>[SIGV4_PROCESSING_BUFFER_LENGTH]</arglist>
    </member>
    <member kind="variable">
      <type>char *</type>
      <name>pBufCur</name>
      <anchorfile>struct_canonical_context__t.html</anchorfile>
      <anchor>a58006d3c9996e0042becf93526e799c3</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>bufRemaining</name>
      <anchorfile>struct_canonical_context__t.html</anchorfile>
      <anchor>a66c22c84c6ca65adb6f030a72a1b1891</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>HmacContext_t</name>
    <filename>struct_hmac_context__t.html</filename>
    <member kind="variable">
      <type>const SigV4CryptoInterface_t *</type>
      <name>pCryptoInterface</name>
      <anchorfile>struct_hmac_context__t.html</anchorfile>
      <anchor>a6022260378710e9672d6bed505082630</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>key</name>
      <anchorfile>struct_hmac_context__t.html</anchorfile>
      <anchor>a7e43fd373ae5ef5180c633ffa66b8642</anchor>
      <arglist>[SIGV4_HASH_MAX_BLOCK_LENGTH]</arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>keyLen</name>
      <anchorfile>struct_hmac_context__t.html</anchorfile>
      <anchor>a567cae8cfccc7935f853d182c0c7ce1d</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4ConstString_t</name>
    <filename>struct_sig_v4_const_string__t.html</filename>
    <member kind="variable">
      <type>const char *</type>
      <name>pData</name>
      <anchorfile>struct_sig_v4_const_string__t.html</anchorfile>
      <anchor>a0f39ef9b3df47ae873966722e561a8f4</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>dataLen</name>
      <anchorfile>struct_sig_v4_const_string__t.html</anchorfile>
      <anchor>a7bf293e77ee8342dabf0cf72a621f183</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4Credentials_t</name>
    <filename>struct_sig_v4_credentials__t.html</filename>
    <member kind="variable">
      <type>const char *</type>
      <name>pAccessKeyId</name>
      <anchorfile>struct_sig_v4_credentials__t.html</anchorfile>
      <anchor>a414515869b58a43398e114c615d19225</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>accessKeyIdLen</name>
      <anchorfile>struct_sig_v4_credentials__t.html</anchorfile>
      <anchor>af9e568fdc4a9228882a47632a08ce647</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pSecretAccessKey</name>
      <anchorfile>struct_sig_v4_credentials__t.html</anchorfile>
      <anchor>a34b2bfc8ec1fd9d977327a010c50142c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>secretAccessKeyLen</name>
      <anchorfile>struct_sig_v4_credentials__t.html</anchorfile>
      <anchor>a21641db40ff66baf3d03fca50500769f</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4CryptoInterface_t</name>
    <filename>struct_sig_v4_crypto_interface__t.html</filename>
    <member kind="variable">
      <type>int32_t(*</type>
      <name>hashInit</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>a381d93f78dc2c36e16edb2a2e24668e5</anchor>
      <arglist>)(void *pHashContext)</arglist>
    </member>
    <member kind="variable">
      <type>int32_t(*</type>
      <name>hashUpdate</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>a24b2758a942de8d6b3a989fbd418687f</anchor>
      <arglist>)(void *pHashContext, const uint8_t *pInput, size_t inputLen)</arglist>
    </member>
    <member kind="variable">
      <type>int32_t(*</type>
      <name>hashFinal</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>a0b9c0d669d8b08b0b57d49785d557f02</anchor>
      <arglist>)(void *pHashContext, uint8_t *pOutput, size_t outputLen)</arglist>
    </member>
    <member kind="variable">
      <type>void *</type>
      <name>pHashContext</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>ace57ee60a700ebd799c694296138d43d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>hashBlockLen</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>a3c22a540288608d12bc9845e2298efe2</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>hashDigestLen</name>
      <anchorfile>struct_sig_v4_crypto_interface__t.html</anchorfile>
      <anchor>a42d88e4f0aaf17bce688ffdd5c99e81a</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4DateTime_t</name>
    <filename>struct_sig_v4_date_time__t.html</filename>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_year</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>ad611e0f4aeefd89029c787a9ff53ed29</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_mon</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>a41b51ae5628debc3779bb44741bec925</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_mday</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>a834e155f404dec102ef40c57dbdee2e1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_hour</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>ad12da817bae30f79e4d1978292c52a4c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_min</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>ac6ee429704fa77ed4d9299b8fe1e6610</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>tm_sec</name>
      <anchorfile>struct_sig_v4_date_time__t.html</anchorfile>
      <anchor>ae6e67557a1a10a75d095da436632b304</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4HttpParameters_t</name>
    <filename>struct_sig_v4_http_parameters__t.html</filename>
    <member kind="variable">
      <type>const char *</type>
      <name>pHttpMethod</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>ae40e818a9c82d9d5fd799318c63e9d9d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>httpMethodLen</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>aea67a40c05bc0c78667ea91fefd157cb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>flags</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a788f7e5646c31e5562f64b4f4336fc3d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pPath</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a0d4d892bd446073378a8d30c99ddfb72</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>pathLen</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a918de9ee338f28a2911a6922a936e62f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pQuery</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>aadb19498e58d35cd8feaa39e30b49d15</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>queryLen</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a5b499a5d2d1858ae55d779354f9d3abb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pHeaders</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a519da616fabd4d2e1deae442bda3d0d7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>headersLen</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>ad2e5ed60470e71d67c8e133422f9d277</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pPayload</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>a76c646fbdb585dc150a390673923505f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>payloadLen</name>
      <anchorfile>struct_sig_v4_http_parameters__t.html</anchorfile>
      <anchor>ad99a445c9494aabe945a20707933923b</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4KeyValuePair_t</name>
    <filename>struct_sig_v4_key_value_pair__t.html</filename>
    <member kind="variable">
      <type>SigV4ConstString_t</type>
      <name>key</name>
      <anchorfile>struct_sig_v4_key_value_pair__t.html</anchorfile>
      <anchor>ad05d13c2101e1b07f1ac0b502a6ed2d6</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>SigV4ConstString_t</type>
      <name>value</name>
      <anchorfile>struct_sig_v4_key_value_pair__t.html</anchorfile>
      <anchor>aaf2daf49a6cddf301490571da03484bc</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4Parameters_t</name>
    <filename>struct_sig_v4_parameters__t.html</filename>
    <member kind="variable">
      <type>SigV4Credentials_t *</type>
      <name>pCredentials</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a5427dc690bbc4abdd61c334aed5cd256</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pDateIso8601</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a841cd5268274f7c7152a8d291e6015aa</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pAlgorithm</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>abacc8103c2faa935211c8aa9c5b6e95b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>algorithmLen</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a7e1e9cbdd65d2219946a500e1f5282a2</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pRegion</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a2c259d0816a815c420509f6ca8ec1ca1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>regionLen</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>ad6ead8df8d99af8e92ebb510ec95b9f9</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>const char *</type>
      <name>pService</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a2617dd8c3a3e1bb354882aff51ec8009</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>serviceLen</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>aee666e124ca0c30f5b4acf715b0a7ac5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>SigV4CryptoInterface_t *</type>
      <name>pCryptoInterface</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a97c3393c1033d2ca544bced05c7c4132</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>SigV4HttpParameters_t *</type>
      <name>pHttpParameters</name>
      <anchorfile>struct_sig_v4_parameters__t.html</anchorfile>
      <anchor>a9797871c5f447cddf75ecee6017ff2e9</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>SigV4String_t</name>
    <filename>struct_sig_v4_string__t.html</filename>
    <member kind="variable">
      <type>char *</type>
      <name>pData</name>
      <anchorfile>struct_sig_v4_string__t.html</anchorfile>
      <anchor>a89e684f1de03d3916bdb9e8ed9d243ca</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>dataLen</name>
      <anchorfile>struct_sig_v4_string__t.html</anchorfile>
      <anchor>aa467527487129abb7a559445dc151dc6</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>sigv4_enum_types</name>
    <title>Enumerated Types</title>
    <filename>group__sigv4__enum__types.html</filename>
    <member kind="enumeration">
      <type></type>
      <name>SigV4Status_t</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>ga9473b37a4c9e1e9b1d45d90b062d8df9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4Success</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a238f75db46434dcb1fa3e8bbdf048627</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InvalidParameter</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9aca7601341caf16c3fb93a0927b9f6ab6</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InsufficientMemory</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a2bb0cb0ecb7f2856a93b9c533d780e7c</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4ISOFormattingError</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a70fb09164f149921dbdabca0909aee1a</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4MaxHeaderPairCountExceeded</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a7201ec16e087837e7e405ae908014479</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4MaxQueryPairCountExceeded</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a717bf762306a480d172b76912f525478</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4HashError</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9a682f99d6afd965cf64411eafc4985de9</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>SigV4InvalidHttpHeaders</name>
      <anchorfile>group__sigv4__enum__types.html</anchorfile>
      <anchor>gga9473b37a4c9e1e9b1d45d90b062d8df9aa535c1f048c34142ee558517b14d6d69</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>sigv4_struct_types</name>
    <title>Struct Types</title>
    <filename>group__sigv4__struct__types.html</filename>
    <class kind="struct">SigV4CryptoInterface_t</class>
    <class kind="struct">SigV4HttpParameters_t</class>
    <class kind="struct">SigV4Credentials_t</class>
    <class kind="struct">SigV4Parameters_t</class>
  </compound>
  <compound kind="group">
    <name>sigv4_canonical_flags</name>
    <title>SigV4HttpParameters_t Flags</title>
    <filename>group__sigv4__canonical__flags.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_PATH_IS_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga65f1081bc8e969ce7bc726d5bc1c5f7b</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_QUERY_IS_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga16fa9ad1cc53594a061985c243c520b9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga9e9136345f456eb4c76bca582a88331f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_ALL_ARE_CANONICAL_FLAG</name>
      <anchorfile>group__sigv4__canonical__flags.html</anchorfile>
      <anchor>ga00b06a304245f49ac6084734046a3cfb</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>sigv4_constants</name>
    <title>Sigv4_constants</title>
    <filename>group__sigv4__constants.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_AWS4_HMAC_SHA256</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaab763fe2fe7acc18bb492c254d762ae3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_AWS4_HMAC_SHA256_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa9e9d97756a1f6389f6da8617170f08c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_DATE_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga0b4b6958b256d0a29275d34e9617c5f4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_SECURITY_TOKEN_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga3c7e4fecb06d49179202bc08b41b82d3</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_STREAMING_AWS4_HMAC_SHA256_PAYLOAD</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga954dd406cb66a2d9140b1e4893d559e2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_CONTENT_SHA256_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaef74844bfe1983b6b84bf18b01cd4c4a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_HTTP_X_AMZ_STORAGE_CLASS_HEADER</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gae3ebc0dbf384ba019f1cd16abd5c7fd6</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_ACCESS_KEY_ID_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gae09d1c889461e9bd3394e5fd41184432</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_SECRET_ACCESS_KEY_LENGTH</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga540d0660078b1f4b7a4ba1b46b3c96ad</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_ISO_STRING_LEN</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa96f2b005c358892fc9ae3f1ecc7f757</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_EXPECTED_LEN_RFC_3339</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>ga5fa31664388d3b37d415c31cfd0674f9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>SIGV4_EXPECTED_LEN_RFC_5322</name>
      <anchorfile>group__sigv4__constants.html</anchorfile>
      <anchor>gaa07110bba8f36cd9e013e33d0f887155</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="page">
    <name>sigv4_config</name>
    <title>Configurations</title>
    <filename>sigv4_config.html</filename>
    <docanchor file="sigv4_config.html">SIGV4_DO_NOT_USE_CUSTOM_CONFIG</docanchor>
    <docanchor file="sigv4_config.html" title="LogError">sigv4_logerror</docanchor>
    <docanchor file="sigv4_config.html" title="LogWarn">sigv4_logwarn</docanchor>
    <docanchor file="sigv4_config.html" title="LogInfo">sigv4_loginfo</docanchor>
    <docanchor file="sigv4_config.html" title="LogDebug">sigv4_logdebug</docanchor>
  </compound>
  <compound kind="page">
    <name>sigv4_functions</name>
    <title>Functions</title>
    <filename>sigv4_functions.html</filename>
  </compound>
  <compound kind="page">
    <name>sigV4_generateHTTPAuthorization_function</name>
    <title>SigV4_GenerateHTTPAuthorization</title>
    <filename>sig_v4_generate_h_t_t_p_authorization_function.html</filename>
  </compound>
  <compound kind="page">
    <name>sigV4_awsIotDateToIso8601_function</name>
    <title>SigV4_AwsIotDateToIso8601</title>
    <filename>sig_v4_aws_iot_date_to_iso8601_function.html</filename>
  </compound>
  <compound kind="page">
    <name>index</name>
    <title>Overview</title>
    <filename>index.html</filename>
    <docanchor file="index.html">sigv4</docanchor>
    <docanchor file="index.html" title="Memory Requirements">sigv4_memory_requirements</docanchor>
    <docanchor file="index.html" title="Design">sigv4_design</docanchor>
  </compound>
</tagfile>
