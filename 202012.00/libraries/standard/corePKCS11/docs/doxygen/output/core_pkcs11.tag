<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20">
  <compound kind="file">
    <name>core_pkcs11.c</name>
    <path>/home/archigup/csdk/libraries/standard/corePKCS11/source/</path>
    <filename>core__pkcs11_8c.html</filename>
    <includes id="core__pkcs11_8h" name="core_pkcs11.h" local="yes" imported="no">core_pkcs11.h</includes>
    <member kind="function" static="yes">
      <type>static CK_RV</type>
      <name>prvOpenSession</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a823383b0a2c3c3a7f7fad292307a3317</anchor>
      <arglist>(CK_SESSION_HANDLE *pxSession, CK_SLOT_ID xSlotId)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xGetSlotList</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a46c41cd94b0ad5eed22d17a59aef73da</anchor>
      <arglist>(CK_SLOT_ID **ppxSlotId, CK_ULONG *pxSlotCount)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePKCS11</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>af9674309915268c89934f5b4ba9dba4e</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePkcs11Token</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a839e3d1d640a1a13b25a49c93d1a05fa</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePkcs11Session</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a54d499d52094e28bdcfb59839e381675</anchor>
      <arglist>(CK_SESSION_HANDLE *pxSession)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xFindObjectWithLabelAndClass</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a6f97ebff17fdfd0f2dc404b2c61010ae</anchor>
      <arglist>(CK_SESSION_HANDLE xSession, char *pcLabelName, CK_ULONG ulLabelNameLen, CK_OBJECT_CLASS xClass, CK_OBJECT_HANDLE_PTR pxHandle)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>vAppendSHA256AlgorithmIdentifierSequence</name>
      <anchorfile>core__pkcs11_8c.html</anchorfile>
      <anchor>a2e58242913103993041305e349913c88</anchor>
      <arglist>(const uint8_t *puc32ByteHashedMessage, uint8_t *puc51ByteHashOidBuffer)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>core_pkcs11.h</name>
    <path>/home/archigup/csdk/libraries/standard/corePKCS11/source/include/</path>
    <filename>core__pkcs11_8h.html</filename>
    <class kind="struct">PKCS11_CertificateTemplate_t</class>
    <member kind="define">
      <type>#define</type>
      <name>CK_PTR</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a423401496b51f5c72a74e5502b47fd7d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>NULL_PTR</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a530f11a96e508d171d28564c8dc20942</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CK_DEFINE_FUNCTION</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>aa21d2a59f7de7ecc92a13e2958bb60b8</anchor>
      <arglist>(returnType, name)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CK_DECLARE_FUNCTION</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a30315d302108bcfb354196f37b16a492</anchor>
      <arglist>(returnType, name)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CK_DECLARE_FUNCTION_POINTER</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>aad472a68fb8e3eb9ba40169f5180b3b7</anchor>
      <arglist>(returnType, name)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>CK_CALLBACK_FUNCTION</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a5235e6437759c93b8189b124c8c807cf</anchor>
      <arglist>(returnType, name)</arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11SHA256_DIGEST_LENGTH</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>ac1020688685b585cda7b9c4f2b78744f</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11ECDSA_P256_SIGNATURE_LENGTH</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>afb0ec19370a0ef13c3ba9e16f2d812c0</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11ECDSA_P256_KEY_BITS</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a7b079f0b4d00704a7528468024f3375a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11RSA_PUBLIC_EXPONENT</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a88b87e958fdc824b82e7970feed64759</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11RSA_2048_MODULUS_BITS</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a53ad7f65ddb35590bc1393411e285127</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11RSA_2048_SIGNATURE_LENGTH</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a7bbb5c3318097a212658f3eaa92c06bb</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11RSA_SIGNATURE_INPUT_LENGTH</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>aaa89dfd906480c38a78efa5e854f3076</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11ELLIPTIC_CURVE_NISTP256</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a2f217cc01f929b02e1a789cc9e908427</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11MAX_LABEL_LENGTH</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>ab94d23efa5d9de9342e45d357153e54e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11DER_ENCODED_OID_P256</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a61aab65f40f1865cfcdbb66aab3c9ffa</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11configIMPORT_PRIVATE_KEYS_SUPPORTED</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a6a4e66ae660556550058473322f5db51</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>pkcs11STUFF_APPENDED_TO_RSA_SIG</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a3ec42bafe82e299acf76e00da9a54168</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePKCS11</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>af9674309915268c89934f5b4ba9dba4e</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xGetSlotList</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a46c41cd94b0ad5eed22d17a59aef73da</anchor>
      <arglist>(CK_SLOT_ID **ppxSlotId, CK_ULONG *pxSlotCount)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePkcs11Session</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a54d499d52094e28bdcfb59839e381675</anchor>
      <arglist>(CK_SESSION_HANDLE *pxSession)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xInitializePkcs11Token</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a839e3d1d640a1a13b25a49c93d1a05fa</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>xFindObjectWithLabelAndClass</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a6f97ebff17fdfd0f2dc404b2c61010ae</anchor>
      <arglist>(CK_SESSION_HANDLE xSession, char *pcLabelName, CK_ULONG ulLabelNameLen, CK_OBJECT_CLASS xClass, CK_OBJECT_HANDLE_PTR pxHandle)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>vAppendSHA256AlgorithmIdentifierSequence</name>
      <anchorfile>core__pkcs11_8h.html</anchorfile>
      <anchor>a2e58242913103993041305e349913c88</anchor>
      <arglist>(const uint8_t *puc32ByteHashedMessage, uint8_t *puc51ByteHashOidBuffer)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>core_pkcs11_pal.h</name>
    <path>/home/archigup/csdk/libraries/standard/corePKCS11/source/include/</path>
    <filename>core__pkcs11__pal_8h.html</filename>
    <member kind="function">
      <type>CK_RV</type>
      <name>PKCS11_PAL_Initialize</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>ad78bacbf90a03e49a93b73fc7f4287ec</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>CK_OBJECT_HANDLE</type>
      <name>PKCS11_PAL_SaveObject</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>aa426d170f01eec0268938577546c2683</anchor>
      <arglist>(CK_ATTRIBUTE_PTR pxLabel, CK_BYTE_PTR pucData, CK_ULONG ulDataSize)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>PKCS11_PAL_DestroyObject</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>a3e5df5f3f2fe4ab8b5b703e90973603f</anchor>
      <arglist>(CK_OBJECT_HANDLE xHandle)</arglist>
    </member>
    <member kind="function">
      <type>CK_OBJECT_HANDLE</type>
      <name>PKCS11_PAL_FindObject</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>aa40ed819a4db63bf1f82ec3a83f7671d</anchor>
      <arglist>(CK_BYTE_PTR pxLabel, CK_ULONG usLength)</arglist>
    </member>
    <member kind="function">
      <type>CK_RV</type>
      <name>PKCS11_PAL_GetObjectValue</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>a5f9deac2fdf2dc0ac52e87f95d3d6fb6</anchor>
      <arglist>(CK_OBJECT_HANDLE xHandle, CK_BYTE_PTR *ppucData, CK_ULONG_PTR pulDataSize, CK_BBOOL *pIsPrivate)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>PKCS11_PAL_GetObjectValueCleanup</name>
      <anchorfile>core__pkcs11__pal_8h.html</anchorfile>
      <anchor>a62b94691f4534e5328eb88362244e308</anchor>
      <arglist>(CK_BYTE_PTR pucData, CK_ULONG ulDataSize)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>core_pki_utils.c</name>
    <path>/home/archigup/csdk/libraries/standard/corePKCS11/source/</path>
    <filename>core__pki__utils_8c.html</filename>
    <includes id="core__pki__utils_8h" name="core_pki_utils.h" local="yes" imported="no">core_pki_utils.h</includes>
    <member kind="define">
      <type>#define</type>
      <name>FAILURE</name>
      <anchorfile>core__pki__utils_8c.html</anchorfile>
      <anchor>a6d58f9ac447476b4e084d7ca383f5183</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>int8_t</type>
      <name>PKI_mbedTLSSignatureToPkcs11Signature</name>
      <anchorfile>core__pki__utils_8c.html</anchorfile>
      <anchor>a7d2768d5e160165af1294e46e21787c4</anchor>
      <arglist>(uint8_t *pxSignaturePKCS, const uint8_t *pxMbedSignature)</arglist>
    </member>
    <member kind="function">
      <type>int8_t</type>
      <name>PKI_pkcs11SignatureTombedTLSSignature</name>
      <anchorfile>core__pki__utils_8c.html</anchorfile>
      <anchor>a089abc57156366d6e5ab137d51e5e60d</anchor>
      <arglist>(uint8_t *pucSig, size_t *pxSigLen)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>core_pki_utils.h</name>
    <path>/home/archigup/csdk/libraries/standard/corePKCS11/source/include/</path>
    <filename>core__pki__utils_8h.html</filename>
    <member kind="function">
      <type>int8_t</type>
      <name>PKI_mbedTLSSignatureToPkcs11Signature</name>
      <anchorfile>core__pki__utils_8h.html</anchorfile>
      <anchor>a7d2768d5e160165af1294e46e21787c4</anchor>
      <arglist>(uint8_t *pxSignaturePKCS, const uint8_t *pxMbedSignature)</arglist>
    </member>
    <member kind="function">
      <type>int8_t</type>
      <name>PKI_pkcs11SignatureTombedTLSSignature</name>
      <anchorfile>core__pki__utils_8h.html</anchorfile>
      <anchor>a089abc57156366d6e5ab137d51e5e60d</anchor>
      <arglist>(uint8_t *pucSig, size_t *pxSigLen)</arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>PKCS11_CertificateTemplate_t</name>
    <filename>struct_p_k_c_s11___certificate_template__t.html</filename>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xObjectClass</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>ab47a88d3c053dc9800fe4f03b9f675b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xSubject</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>a7239b6cff4ffa2b63d88b149d52e3d8a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xCertificateType</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>a94d315d61728f981137572ea4a0c9f4c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xValue</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>a028ec980b8dca55b842ae0bf1657907f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xLabel</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>ae4fa330e581803d900d1d2b05cbbe52b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>CK_ATTRIBUTE</type>
      <name>xTokenObject</name>
      <anchorfile>struct_p_k_c_s11___certificate_template__t.html</anchorfile>
      <anchor>aaf1210b30b9b00d4ad9d8165b7e7bc38</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="page">
    <name>pkcs11_design</name>
    <title>Design</title>
    <filename>pkcs11_design.html</filename>
    <docanchor file="pkcs11_design.html" title="Memory Requirements">pkcs11_memory_requirements</docanchor>
    <docanchor file="pkcs11_design.html" title="PKCS #11 Wrapper Dependencies">PKCS11_Wrapper</docanchor>
    <docanchor file="pkcs11_design.html" title="PKCS #11 Software Implementation Dependencies">PKCS11_implementation</docanchor>
    <docanchor file="pkcs11_design.html" title="PKCS #11 Utilities Dependencies">PKCS11_utilities</docanchor>
  </compound>
  <compound kind="page">
    <name>pkcs11_seq</name>
    <title>PKCS #11 Sequence Diagrams</title>
    <filename>pkcs11_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_rng_seq</name>
    <title>PKCS #11 RNG Sequence Diagram</title>
    <filename>pkcs11_rng_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_dig_seq</name>
    <title>PKCS #11 Digest Sequence Diagram</title>
    <filename>pkcs11_dig_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_obj_imp_seq</name>
    <title>PKCS #11 Object Import Sequence Diagram</title>
    <filename>pkcs11_obj_imp_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_obj_gen_seq</name>
    <title>PKCS #11 Generate Key Pair Sequence Diagram</title>
    <filename>pkcs11_obj_gen_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_sign_verify_seq</name>
    <title>PKCS #11 Sign and Verify Sequence Diagram</title>
    <filename>pkcs11_sign_verify_seq.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_config</name>
    <title>PKCS #11 Configuration Macros</title>
    <filename>pkcs11_config.html</filename>
    <docanchor file="pkcs11_config.html">configPKCS11_DEFAULT_USER_PIN</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configMAX_LABEL_LENGTH</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configMAX_NUM_OBJECTS</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configMAX_SESSIONS</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11testIMPORT_PRIVATE_KEY_SUPPORT</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11testGENERATE_KEYPAIR_SUPPORT</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11testPREPROVISIONED_SUPPORT</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configPAL_DESTROY_SUPPORTED</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS</docanchor>
    <docanchor file="pkcs11_config.html">pkcs11configLABEL_ROOT_CERTIFICATE</docanchor>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_mbedtls_function</name>
    <title>PKCS #11 mbed TLS Implementation Functions</title>
    <filename>pkcs11_core_mbedtls_function.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_initialize</name>
    <title>C_Initialize</title>
    <filename>pkcs11_mbedtls_function_c_initialize.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_finalize</name>
    <title>C_Finalize</title>
    <filename>pkcs11_mbedtls_function_c_finalize.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_getfunctionlist</name>
    <title>C_GetFunctionList</title>
    <filename>pkcs11_mbedtls_function_c_getfunctionlist.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_getslotlist</name>
    <title>C_GetSlotList</title>
    <filename>pkcs11_mbedtls_function_c_getslotlist.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_gettokeninfo</name>
    <title>C_GetTokenInfo</title>
    <filename>pkcs11_mbedtls_function_c_gettokeninfo.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_getmechanisminfo</name>
    <title>C_GetMechanismInfo</title>
    <filename>pkcs11_mbedtls_function_c_getmechanisminfo.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_inittoken</name>
    <title>C_InitToken</title>
    <filename>pkcs11_mbedtls_function_c_inittoken.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_opensession</name>
    <title>C_OpenSession</title>
    <filename>pkcs11_mbedtls_function_c_opensession.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_closesession</name>
    <title>C_CloseSession</title>
    <filename>pkcs11_mbedtls_function_c_closesession.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_login</name>
    <title>C_Login</title>
    <filename>pkcs11_mbedtls_function_c_login.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_createobject</name>
    <title>C_CreateObject</title>
    <filename>pkcs11_mbedtls_function_c_createobject.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_destroyobject</name>
    <title>C_DestroyObject</title>
    <filename>pkcs11_mbedtls_function_c_destroyobject.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_getattributevalue</name>
    <title>C_GetAttributeValue</title>
    <filename>pkcs11_mbedtls_function_c_getattributevalue.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_findobjectsinit</name>
    <title>C_FindObjectsInit</title>
    <filename>pkcs11_mbedtls_function_c_findobjectsinit.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_findobjects</name>
    <title>C_FindObjects</title>
    <filename>pkcs11_mbedtls_function_c_findobjects.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_findobjectsfinal</name>
    <title>C_FindObjectsFinal</title>
    <filename>pkcs11_mbedtls_function_c_findobjectsfinal.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_digestinit</name>
    <title>C_DigestInit</title>
    <filename>pkcs11_mbedtls_function_c_digestinit.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_digestupdate</name>
    <title>C_DigestUpdate</title>
    <filename>pkcs11_mbedtls_function_c_digestupdate.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_digestfinal</name>
    <title>C_DigestFinal</title>
    <filename>pkcs11_mbedtls_function_c_digestfinal.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_signinit</name>
    <title>C_SignInit</title>
    <filename>pkcs11_mbedtls_function_c_signinit.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_verifyinit</name>
    <title>C_VerifyInit</title>
    <filename>pkcs11_mbedtls_function_c_verifyinit.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_verify</name>
    <title>C_Verify</title>
    <filename>pkcs11_mbedtls_function_c_verify.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_generatekeypair</name>
    <title>C_GenerateKeyPair</title>
    <filename>pkcs11_mbedtls_function_c_generatekeypair.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_mbedtls_function_c_generate_random</name>
    <title>C_GenerateRandom</title>
    <filename>pkcs11_mbedtls_function_c_generate_random.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_wrapper_function</name>
    <title>PKCS #11 Wrapper Functions</title>
    <filename>pkcs11_core_wrapper_function.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_xinitializepkcs11</name>
    <title>xInitializePKCS11</title>
    <filename>pkcs11_core_xinitializepkcs11.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_xgetslotlist</name>
    <title>xGetSlotList</title>
    <filename>pkcs11_core_xgetslotlist.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_xinitializepkcs11token</name>
    <title>xInitializePkcs11Token</title>
    <filename>pkcs11_core_xinitializepkcs11token.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_xinitializepkcs11session</name>
    <title>xInitializePkcs11Session</title>
    <filename>pkcs11_core_xinitializepkcs11session.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_xfindobjectwithlabelandclass</name>
    <title>xFindObjectWithLabelAndClass</title>
    <filename>pkcs11_core_xfindobjectwithlabelandclass.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_vappendsha256algorithmidentifiersequence</name>
    <title>vAppendSHA256AlgorithmIdentifierSequence</title>
    <filename>pkcs11_core_vappendsha256algorithmidentifiersequence.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_pal_function</name>
    <title>PKCS #11 PAL Functions</title>
    <filename>pkcs11_core_pal_function.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_initialize</name>
    <title>PKCS11_PAL_Initialize</title>
    <filename>pkcs11_pal_initialize.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_saveobject</name>
    <title>PKCS11_PAL_SaveObject</title>
    <filename>pkcs11_pal_saveobject.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_destroyobject</name>
    <title>PKCS11_PAL_DestroyObject</title>
    <filename>pkcs11_pal_destroyobject.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_findobject</name>
    <title>PKCS11_PAL_FindObject</title>
    <filename>pkcs11_pal_findobject.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_getobjectvalue</name>
    <title>PKCS11_PAL_GetObjectValue</title>
    <filename>pkcs11_pal_getobjectvalue.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_pal_getobjectvaluecleanup</name>
    <title>PKCS11_PAL_GetObjectValueCleanup</title>
    <filename>pkcs11_pal_getobjectvaluecleanup.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_core_utils_function</name>
    <title>PKCS #11 Utils Functions</title>
    <filename>pkcs11_core_utils_function.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_utils_pkipkcs11signaturetombedtlssignature</name>
    <title>PKI_mbedTLSSignatureToPkcs11Signature</title>
    <filename>pkcs11_utils_pkipkcs11signaturetombedtlssignature.html</filename>
  </compound>
  <compound kind="page">
    <name>pkcs11_utils_pkimbedtlssignaturetopkcs11signature</name>
    <title>PKI_pkcs11SignatureTombedTLSSignature</title>
    <filename>pkcs11_utils_pkimbedtlssignaturetopkcs11signature.html</filename>
  </compound>
  <compound kind="page">
    <name>index</name>
    <title></title>
    <filename>index.html</filename>
    <docanchor file="index.html">core_pkcs11</docanchor>
  </compound>
</tagfile>
