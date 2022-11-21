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

On the Greengrass core, run the following command:

```sh
openssl req -x509 -new -nodes -key ca.key -sha256 -days 1826 -out ca.crt
```

This will create a custom CA cert ca.crt and private key ca.key.

### Configuring the GG core for local auth and MQTT

Deploy the following components to your Greengrass core:
- aws.greengrass.clientdevices.Auth
- aws.greengrass.clientdevices.mqtt.Moquette
- aws.greengrass.clientdevices.mqtt.Bridge
- aws.greengrass.clientdevices.IPDetector

Set the configuration for the aws.greengrass.clientdevices.Auth component based
off the [provided config](./greengrass_auth_conf.json). Ensure the certificate
paths match the files created for your custom CA above.

This config will allow associated Things to publish and subscribe to any topic
on the Greengrass core broker.

In the page for the Greengrass core in your AWS account, ensure that you
associate your Thing with the Greengrass core under the Cloud Discovery tab.

Afterwards, you can configure and run this demo.
