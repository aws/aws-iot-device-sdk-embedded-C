#! /bin/bash

set -exu

curl -X POST \
  https://beta.us-east-1.iot.amazonaws.com/provisioning-templates/ \
  -H 'Authorization: AWS4-HMAC-SHA256 Credential=AKIAXJ6FDD6N2RBM536F/20191102/us-east-1/execute-api/aws4_request, SignedHeaders=content-type;host;x-amz-content-sha256;x-amz-date, Signature=ead8cd6b68a209070db3193e8088c9ee0c6185b6e26fdff4c3813978c908582e' \
  -H 'Content-Type: application/json' \
  -H 'Host: beta.us-east-1.iot.amazonaws.com' \
  -H 'Postman-Token: 8cc79bd8-7906-4234-8667-f3f65a9eee40' \
  -H 'X-Amz-Content-Sha256: adb660c1d50a14fc5383727d2226a4f0281ac1086152f58ee656efcf907bc329' \
  -H 'X-Amz-Date: 20191102T002341Z' \
  -H 'cache-control: no-cache' \
  -d '{
	"provisioningRoleArn": "arn:aws:iam::502387646363:role/Admin",
	"templateName": "Temp2",
	"description": "something",
	"templateBody": "{\r\n  \"Parameters\" : {\r\n     \"DeviceLocation\": {\r\n       \"Type\": \"String\"\r\n     }\r\n  },\r\n\r\n  \"Mappings\": {\r\n    \"LocationTable\": {\r\n      \"Seattle\": {\r\n        \"LocationUrl\": \"https:\/\/example.aws\"\r\n      }\r\n    }\r\n  },\r\n\r\n  \"Resources\" : {\r\n    \"thing\" : {\r\n      \"Type\" : \"AWS::IoT::Thing\",\r\n      \"Properties\" : {\r\n        \"ThingName\" : \"ThingName\",\r\n        \"AttributePayload\" : { \"version\" : \"v1\", \"serialNumber\" : \"serialNumber\"},\r\n        \"ThingTypeName\" :  \"lightBulb-versionA\",\r\n        \"ThingGroups\" : [\"v1-lightbulbs\", \"WA\"],\r\n        \"BillingGroup\": \"BillingGroup\"\r\n      },\r\n      \"OverrideSettings\" : {\r\n        \"AttributePayload\" : \"MERGE\",\r\n        \"ThingTypeName\" : \"REPLACE\",\r\n        \"ThingGroups\" : \"DO_NOTHING\"\r\n      }\r\n    },\r\n\r\n    \"certificate\" : {\r\n      \"Type\" : \"AWS::IoT::Certificate\",\r\n      \"Properties\" : {\r\n        \"Status\" : \"Active\"\r\n      },\r\n      \"OverrideSettings\" : {\r\n        \"Status\" : \"DO_NOTHING\"\r\n      }\r\n    },\r\n\r\n    \"policy\" : {\r\n      \"Type\" : \"AWS::IoT::Policy\",\r\n      \"Properties\" : {\r\n        \"PolicyDocument\" : {\r\n          \"Version\": \"2012-10-17\",\r\n          \"Statement\": [{\r\n            \"Effect\": \"Allow\",\r\n            \"Action\":[\"iot:Publish\"],\r\n            \"Resource\": [\"arn:aws:iot:us-east-1:123456789012:topic\/foo\/bar\"]\r\n          }]\r\n        }\r\n      }\r\n    }\r\n  },\r\n\r\n  \"DeviceConfiguration\": {\r\n    \"FallbackUrl\": \"https:\/\/www.example.com\/test-site\",\r\n    \"LocationUrl\": {\"Fn::FindInMap\": [\"LocationTable\", {\"Ref\": \"DeviceLocation\"}, \"LocationUrl\"]}\r\n  }\r\n}\r\n}",
	"enabled": true
}'