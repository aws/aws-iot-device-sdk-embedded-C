## Setup for Fleet Provisioning Demos

### Create the Provisioning Policy

1. Log in to your AWS account and open AWS IoT Core.
2. Navigate to Security > Policies > Create policy.
3. Enter a relevant policy name.
4. Copy the contents from demos/fleet_provisioning/fleet_provisioning_with_csr (or fleet_provisioning_keys_cert_demo)/example_claim_policy.json.
5. Paste the copied content into the policy document on the AWS console.
6. Click "Create policy".

### Create the Claim Certificate
1. In AWS IoT Core, go to Security > Certificates > Add certificate.
2. Set the "Certificate Status" to active.
3. Download the certificate files from the provided prompt.
4. Update the demo_config.h file:
    - Set CLAIM_CERT_PATH to the path of the downloaded certificate.
    - Set CLAIM_PRIVATE_KEY_PATH to the path of the downloaded private key. Note: You can also set these values using command line parameters.
5. Select the certificate, click "Attach policies", choose your provisioning policy, and click "Attach policy".

### Create the IAM Role for AWS IoT
1. Go to the IAM Identity Center.
2. Create a new IAM role.
3. When prompted, select AWS IoT as the service.

### Create Fleet Provisioning Template
1. Navigate to AWS IoT Core > Connect many devices > Connect many devices > Create provisioning template.
2. Choose "Provisioning devices with claim certificates" and click "Next".
3. Set the status to active.
4. Enter a template name.
5. Select the IAM role you created earlier (or create a new one if needed).
6. Choose the provisioning policy you created earlier (or create a new one if needed).
7. Select "Don't use a pre-provisioning action".
8. Enable the automatic thing creation option and click "Next".
9. Select or create a policy for your device's permissions (e.g., connecting to IoT, subscribing/publishing to topics).
10. Click "Next", review the settings, and create the template.

### Configure the Demo
Set all necessary macro values in the demo_config.h file. Alternatively, you can provide these values through command line parameters.