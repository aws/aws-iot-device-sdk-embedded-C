<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20" doxygen_gitid="f246dd2f1c58eea39ea3f50c108019e4d4137bd5">
  <compound kind="file">
    <name>core_json.c</name>
    <path>C:/b/aws-iot-device-sdk-embedded-c-fork/libraries/standard/coreJSON/source/</path>
    <filename>core__json_8c.html</filename>
    <includes id="core__json_8h" name="core_json.h" local="yes" imported="no">core_json.h</includes>
    <member kind="function">
      <type>JSONStatus_t</type>
      <name>JSON_Validate</name>
      <anchorfile>core__json_8c.html</anchorfile>
      <anchor>af4eb1eb1e2a2563abd0d5404b04aa9ff</anchor>
      <arglist>(const char *buf, size_t max)</arglist>
    </member>
    <member kind="function">
      <type>JSONStatus_t</type>
      <name>JSON_Search</name>
      <anchorfile>core__json_8c.html</anchorfile>
      <anchor>a5baf32463b68637ec2b51376546f5d15</anchor>
      <arglist>(char *buf, size_t max, const char *query, size_t queryLength, char **outValue, size_t *outValueLength)</arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>core_json.h</name>
    <path>C:/b/aws-iot-device-sdk-embedded-c-fork/libraries/standard/coreJSON/source/include/</path>
    <filename>core__json_8h.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>MAX_INDEX_VALUE</name>
      <anchorfile>core__json_8h.html</anchorfile>
      <anchor>aef79ff8de4cb794d9b5415a403119607</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumeration">
      <type></type>
      <name>JSONStatus_t</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>ga2b720193877345b237518677216f00a0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONPartial</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0ae06fe683a38c3fbd8cf55f0324c4a1ac</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONSuccess</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a6b579c45491843ff8dbc535fb17a0402</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONIllegalDocument</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a5a11baf84e1d3a36dd78c3e87b420d4b</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONMaxDepthExceeded</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a95c8555b742422f8a4a3d47f586082f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONNotFound</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a2f53f1dedfe8a356102000360cab5c4d</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONNullParameter</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0ac600e51779a633bc071b876e1b8144a0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONBadParameter</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a8bdd764c656184f942d493fecd12afb1</anchor>
      <arglist></arglist>
    </member>
    <member kind="function">
      <type>JSONStatus_t</type>
      <name>JSON_Validate</name>
      <anchorfile>core__json_8h.html</anchorfile>
      <anchor>af4eb1eb1e2a2563abd0d5404b04aa9ff</anchor>
      <arglist>(const char *buf, size_t max)</arglist>
    </member>
    <member kind="function">
      <type>JSONStatus_t</type>
      <name>JSON_Search</name>
      <anchorfile>core__json_8h.html</anchorfile>
      <anchor>a5baf32463b68637ec2b51376546f5d15</anchor>
      <arglist>(char *buf, size_t max, const char *query, size_t queryLength, char **outValue, size_t *outValueLength)</arglist>
    </member>
  </compound>
  <compound kind="group">
    <name>json_enum_types</name>
    <title>Enumerated Types</title>
    <filename>group__json__enum__types.html</filename>
    <member kind="enumeration">
      <type></type>
      <name>JSONStatus_t</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>ga2b720193877345b237518677216f00a0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONPartial</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0ae06fe683a38c3fbd8cf55f0324c4a1ac</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONSuccess</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a6b579c45491843ff8dbc535fb17a0402</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONIllegalDocument</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a5a11baf84e1d3a36dd78c3e87b420d4b</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONMaxDepthExceeded</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a95c8555b742422f8a4a3d47f586082f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONNotFound</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a2f53f1dedfe8a356102000360cab5c4d</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONNullParameter</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0ac600e51779a633bc071b876e1b8144a0</anchor>
      <arglist></arglist>
    </member>
    <member kind="enumvalue">
      <name>JSONBadParameter</name>
      <anchorfile>group__json__enum__types.html</anchorfile>
      <anchor>gga2b720193877345b237518677216f00a0a8bdd764c656184f942d493fecd12afb1</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="page">
    <name>json_design</name>
    <title>Design</title>
    <filename>json_design.html</filename>
  </compound>
  <compound kind="page">
    <name>json_functions</name>
    <title>Functions</title>
    <filename>json_functions.html</filename>
  </compound>
  <compound kind="page">
    <name>json_validate_function</name>
    <title>JSON_Validate</title>
    <filename>json_validate_function.html</filename>
  </compound>
  <compound kind="page">
    <name>json_search_function</name>
    <title>JSON_Search</title>
    <filename>json_search_function.html</filename>
  </compound>
  <compound kind="page">
    <name>index</name>
    <title>Overview</title>
    <filename>index.html</filename>
    <docanchor file="index.html">json</docanchor>
    <docanchor file="index.html" title="Memory Requirements">json_memory_requirements</docanchor>
  </compound>
</tagfile>
