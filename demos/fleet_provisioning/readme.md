## Setup for Fleet Provisioning Demos

### Creating the Provisioning Policy

1. Login to your AWS account and open AWS IoT Core. On the side bar click on security > policies > create policy
2. Set a relevant policy name
3. Copy the contents in the demos/fleet_provisioning/fleet_provisioning_with_csr(or fleet_provisioning_keys_cert_demo)/example_claim_policy.json and paste it in the policy document on the AWS console.
4. Create the policy


### Creating the Claim Certificate

1. On the side bar of the AWS IoT Core click on security > certificates > add certificate. Make the “Certificate Status” active and download the certificate files from the prompt given.
2. Set the value of the macro CLAIM_CERT_PATH in the democonfig.h file to the path of the certificate downloaded and set the value of the macro CLAIM_PRIVATE_KEY_PATH in the democonfig.h file to the path of the private key downloaded. Alternatively you can set the values of these through command line parameters.
3. Now click on the certificate > attach policies > select your provisioning policy made in the previous section and select attach policy.


### Creating the IAM role for AWS IoT to create resources

1. Go to the IAM Identity center and create a new IAM role
2. Select AWS IoT when asked to select a service


### Creating Fleet Provisioning Template

1. Go to AWS IoT Core > Connect many devices > Connect many devices > create provisioning template.
2. Select Provisioning devices with claim certificates > next
3. Set the status to active
4. Enter template name
5. Enter the IAM role you created in the previous section or you can create a new one if you have not yet created it
6. Enter the provisioning policy that you made in the very first section or create a new one if you havn’t already
7. We do not need to do any pre-provisioning stuff hence we will select “Don’t use a pre-provisioning action”
8. Turn the automatic thing creation option on and click next
9. Select a policy that you wish your device should have when it is running (Permissions to connet to IoT, subscribe to some topic, publish to some topic extra) or make a new one if you do not have one already.
10. Click next, review and create.

### Configuring the demo
Set all the necessary macro values in the demo_config.h file or alternatively you can set the values of these through command line parameters.

