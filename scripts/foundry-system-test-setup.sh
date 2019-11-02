#! /bin/bash

set -exu

curl -X POST \
  https://beta.us-east-1.iot.amazonaws.com/provisioning-templates/ \
  -H 'Authorization: AWS4-HMAC-SHA256 Credential=AKIA2MNYHO3QFGVA55BA/20191102/us-east-1/execute-api/aws4_request, SignedHeaders=content-type;host;x-amz-content-sha256;x-amz-date, Signature=53a2fb52c4b344e26556ebd2d62e462d698b8ab73a996986b62734708d86140a' \
  -H 'Content-Type: application/json' \
  -H 'Host: beta.us-east-1.iot.amazonaws.com' \
  -H 'Postman-Token: bcb8192f-b103-4708-8b72-c84322fbb5f3' \
  -H 'X-Amz-Content-Sha256: adb660c1d50a14fc5383727d2226a4f0281ac1086152f58ee656efcf907bc329' \
  -H 'X-Amz-Date: 20191102T013454Z' \
  -H 'cache-control: no-cache' \
  -d '{
	"provisioningRoleArn": "arn:aws:iam::502387646363:role/Admin",
	"templateName": "Temp2",
	"description": "something",
	"templateBody": "{\r\n  \"Parameters\" : {\r\n     \"DeviceLocation\": {\r\n       \"Type\": \"String\"\r\n     }\r\n  },\r\n\r\n  \"Mappings\": {\r\n    \"LocationTable\": {\r\n      \"Seattle\": {\r\n        \"LocationUrl\": \"https:\/\/example.aws\"\r\n      }\r\n    }\r\n  },\r\n\r\n  \"Resources\" : {\r\n    \"thing\" : {\r\n      \"Type\" : \"AWS::IoT::Thing\",\r\n      \"Properties\" : {\r\n        \"ThingName\" : \"ThingName\",\r\n        \"AttributePayload\" : { \"version\" : \"v1\", \"serialNumber\" : \"serialNumber\"},\r\n        \"ThingTypeName\" :  \"lightBulb-versionA\",\r\n        \"ThingGroups\" : [\"v1-lightbulbs\", \"WA\"],\r\n        \"BillingGroup\": \"BillingGroup\"\r\n      },\r\n      \"OverrideSettings\" : {\r\n        \"AttributePayload\" : \"MERGE\",\r\n        \"ThingTypeName\" : \"REPLACE\",\r\n        \"ThingGroups\" : \"DO_NOTHING\"\r\n      }\r\n    },\r\n\r\n    \"certificate\" : {\r\n      \"Type\" : \"AWS::IoT::Certificate\",\r\n      \"Properties\" : {\r\n        \"Status\" : \"Active\"\r\n      },\r\n      \"OverrideSettings\" : {\r\n        \"Status\" : \"DO_NOTHING\"\r\n      }\r\n    },\r\n\r\n    \"policy\" : {\r\n      \"Type\" : \"AWS::IoT::Policy\",\r\n      \"Properties\" : {\r\n        \"PolicyDocument\" : {\r\n          \"Version\": \"2012-10-17\",\r\n          \"Statement\": [{\r\n            \"Effect\": \"Allow\",\r\n            \"Action\":[\"iot:Publish\"],\r\n            \"Resource\": [\"arn:aws:iot:us-east-1:123456789012:topic\/foo\/bar\"]\r\n          }]\r\n        }\r\n      }\r\n    }\r\n  },\r\n\r\n  \"DeviceConfiguration\": {\r\n    \"FallbackUrl\": \"https:\/\/www.example.com\/test-site\",\r\n    \"LocationUrl\": {\"Fn::FindInMap\": [\"LocationTable\", {\"Ref\": \"DeviceLocation\"}, \"LocationUrl\"]}\r\n  }\r\n}\r\n}",
	"enabled": true
}'