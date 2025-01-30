# Greengrass local auth demo

This demo shows connecting a device using coreMQTT to a Greengrass core using
local authentication. This feature is available since version [v2.9.0](https://docs.aws.amazon.com/greengrass/v2/developerguide/greengrass-release-2022-11-15.html)

Connecting to a Greengrass core is similar to connecting to IoT core. The
device's Thing will need to be registered on IoT core just as with connecting
directly. When setting up the Greengrass core, use your own Root CA, and
provision the connecting device with the Root CA used for the Greengrass core.

To read more about using Greengrass with custom CAs, see the docs on
[offline authentication](https://docs.aws.amazon.com/greengrass/v2/developerguide/offline-authentication.html).

This demo uses macros in demo_config.h for provisioned data; the following need
to be set:

- `GREENGRASS_ADDRESS`
  - Set this to the IP of the Greengrass core.
- `ROOT_CA_CERT_PATH`
  - Set this to the path to the CA certificate for the Greengrass core custom
    CA.
- `CLIENT_CERT_PATH`
  - Set this to the client cert downloaded from IoT core when setting up the
    Thing.
- `CLIENT_PRIVATE_KEY_PATH`
  - Set this to the client private key downloaded from IoT core when setting up
    the Thing.
- `THING_NAME`
  - Set this to the Thing name configured in IoT core.

These macros can also be set on the cmake command like follows:

```sh
cmake -S . -Bbuild -DGREENGRASS_ADDRESS="<your-gg-core-ip>" -DROOT_CA_CERT_PATH="<your-path-to-custom-root-ca>" -DCLIENT_CERT_PATH="<your-client-certificate-path>" -DCLIENT_PRIVATE_KEY_PATH="<your-client-private-key-path>" -DTHING_NAME="<your-registered-thing-name>"
```

## Setting up the prerequisites

### Creating the Thing

See the [Getting Started section of the README](../../../README.md#getting-started)
for setting up this repo and your AWS IoT account. Use the Thing credentials
generated for the above macros.

### Setting up a Greengrass Core

For setting up the Greengrass core, see [the Greengrass getting started guide](https://docs.aws.amazon.com/greengrass/v2/developerguide/getting-started.html)

### Creating a custom CA

Next you will need to set up a Root CA for your Greengrass device.

On the Greengrass core, run the following:

1. Create private key for the CA certificate
```sh
openssl genrsa -out ca.key 2048
```
2. Use the private key of CA to generate a self signed certificate
```sh
openssl req -x509 -new -nodes \
-key ca.key \
-sha256 -days 1024 \
-out ca.pem
```
3. Create a private key for the Thing device.
```sh
openssl genrsa -out thing_private.key 2048
```
4. Using the private key, create a certificate signing request
```sh
openssl req -new \
-key thing_private.key \
-out thing_csr.csr
```
5. Using the CSR, root CA and private key of root CA , create the client certificate
```sh
openssl x509 -req \
-in thing_csr.csr \
-CA ca.pem \
-CAkey ca.key \
-CAcreateserial \
-out thing_cert.pem \
-days 500 -sha256
```
6. Register the CA certificate to AWS IoT by going to AWS console → AWS IoT → Security → Certificates authorities → Register CA certificate. Upload the CA certificate and CA status to active, leave other settings as default. Click on Register.

7. Register the Device certificate to AWS IoT

    * Go to console → AWS IoT → Security → Certificates → Add certificate → Register certificates.
    * Select your Registered CA from the dropdown.
    * Upload your device certificate (thing_cert.pem) and Activate it by selecting the certificate and clicking on the Activate button

8. Create a new thing and link it with this new certificate thing_cert.pem and set the value of the macro `THING_NAME` in demo_config.h file to the name of this new thing

9. Set the value of the macro `CLIENT_CERT_PATH` to the path of thing_cert.pem and the value of the macro `CLIENT_PRIVATE_KEY_PATH` to the path of thing_private.key

### Configuring the GG core for local auth and MQTT

Deploy the following components to your Greengrass core:
- aws.greengrass.clientdevices.Auth
- aws.greengrass.clientdevices.mqtt.Moquette
- aws.greengrass.clientdevices.mqtt.Bridge
- aws.greengrass.clientdevices.IPDetector

Set the configuration for the aws.greengrass.clientdevices.Auth component based
off the [provided config](./greengrass_auth_conf.json). Ensure the certificate
paths match the files created for your custom CA above and their absolute paths are written after `file://`.

This config will allow associated Things to publish and subscribe to any topic
on the Greengrass core broker.

In the page for the Greengrass core in your AWS account, ensure that you
associate your Thing with the Greengrass core under the Cloud Discovery tab.

Afterwards, you can configure and run this demo.
