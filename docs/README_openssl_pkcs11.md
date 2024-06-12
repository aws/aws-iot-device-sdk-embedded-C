# Install Prerequisites
Install the prerequisites for using openssl with the libp11 pkcs11 engine:
```
sudo apt install softhsm2 gnutls-bin openssl libengine-pkcs11-openssl libp11-kit0 libp11-kit-dev p11-kit p11-kit-modules
```

[SoftHSM2](https://github.com/opendnssec/SoftHSMv2) is used as the pkcs11 module in this documentation. It should be replaced with the actual pkcs11 module you plan to use in production.

If running softhsm on a linux system, be sure to add your user to the "softhsm" group and log-out/log-in if required by your distribution.
```
sudo adduser $(whoami) softhsm
```

# Initialize token and list objects
List existing tokens:
```
export GNUTLS_SO_PIN=0000
export GNUTLS_PIN=0000
p11tool --login --list-all
```

## SoftHSM2
SoftHSM2 is used as an example PKCS#11 module for testing purposes. Depending on your device security model, it may or may not be suitable for use in produiction.


Delete any existing tokens if desired:
```
softhsm2-util --delete-token --token default
```
Initalize a new token:
```
softhsm2-util --init-token --free --label default --pin 0000 --so-pin 0000
```

Check that the new token is accessible:
```
softhsm2-util --show-slots
```

When using p11-kit-proxy, SoftHSM should be automatically detected by the openssl pkcs11 engine.

## p11-kit-trust
P11-Kit includes a Turst Policy module which exposes the trusted CA certificates installed on a system via PKCS#11.

Note: By default, this module has the "disable-in: p11-kit-proxy" configuration option set. This will cause p11-kit-proxy to disregard this module altogether. If you plan to use PKCS#11 to access to the system trust store, you may want to disable this confgiuration option to allow access to both the system trust store and the PKCS11 module containing your private key.

## Microchip CryptoAuthLib for ECC608
[cryptoauthlib](https://github.com/MicrochipTech/cryptoauthlib)

## p11-kit-proxy
On linux systems, it is quite common to use the [p11-kit-proxy](https://p11-glue.github.io/p11-glue/p11-kit.html) PKCS#11 module to arbitrate access to one or more other PKCS#11 modules from one or more threads.

p11-kit and other p11-kit aware packages install default "module" configuration files in /usr/share/p11-kit/modules/. p11-kit also searches /etc/pkcs11/modules and ~/.config/pkcs11/modules for additional user-defined module configurations.

The Openssl PKCS#11 module is configured to use p11-kit-proxy by default in most linux distributions.

# Generate a new Key
Generate a new public/private key pair if one has not been pre-provisioned in your hsm.
ECC/ECDSA keys typically have a lower computational overhead, so are preferred on low-resource devices.
Generate either an RSA or ECDSA key.

## Delete any existing key objects
```
yes | p11tool --login --delete "pkcs11:object=aws_iot_pk"
```
## RSA
```
p11tool --login --generate-rsa --bits 2048 --label "aws_iot_pk" pkcs11:token=default
```
## ECC / ECDSA
```
p11tool --login --generate-ecc --curve secp256r1 --label "aws_iot_pk" pkcs11:token=default
```

# Generate and register a certificate
A certificate can be generated in any of the three ways listed in the following sections. Choose the option that best fits your device provisioning strategy.

## Self-Signed Certificate
```
openssl req -new -x509 -subj '/CN=TestIotDevice01/' -days 30 -sha256 -engine pkcs11 -keyform engine -key "pkcs11:object=aws_iot_pk" -outform pem -out aws_iot_pk.crt -passin pass:0000
```
Review the contents of the self-signed certificate:
```
openssl x509 -in aws_iot_pk.crt -noout -text
```
Register the self-signed certificate with AWS IoT Core
```
aws iot register-certificate-without-ca --status=ACTIVE --certificate-pem file://aws_iot_pk.crt
```
## Certificate Signed by a private CA registered with IoT Core
Follow the guides listed below to generate a new Certificate Authority and register that CA with AWS IoT Core.

[Generate a new CA](https://docs.aws.amazon.com/iot/latest/developerguide/create-your-CA-cert.html)

[Register your new CA with AWS IoT Core](https://docs.aws.amazon.com/iot/latest/developerguide/register-CA-cert.html)

Generate a new CSR
```
openssl req -new -subj '/CN=TestIotDevice01/' -sha256 -engine pkcs11 -keyform engine -key "pkcs11:object=aws_iot_pk" -outform pem -out aws_iot_pk.csr -passin pass:0000
```
View the contents of the generated CSR
```
openssl x509 -in aws_iot_pk.csr -noout -text
```
Issue a Certificate from you CA

Follow the instructions for your particular CA managerment software or using something similar to the openssl command below:
```
openssl x509 -req \
    -in device_cert_csr_filename \
    -CA root_CA_pem_filename \
    -CAkey root_CA_key_filename \
    -CAcreateserial \
    -out device_cert_pem_filename \
    -days 500 -sha256
```

## Certificate Signed by AWS IoT Core
Generate a new CSR
```
openssl req -new -subj '/CN=TestIotDevice01/' -sha256 -engine pkcs11 -keyform engine -key "pkcs11:object=aws_iot_pk" -outform pem -out aws_iot_pk.csr -passin pass:0000
```
View the contents of the generated CSR
```
openssl x509 -in aws_iot_pk.csr -noout -text
```
Submit the CSR to IoT Core, receive the new certificate and register it via the aws cli
```
aws iot create-certificate-from-csr --set-as-active --certificate-signing-request file://aws_iot_pk.csr --certificate-pem-outfile aws_iot_pk.crt
```

# Import certificate back into HSM
Next, import the generated certificate back into your HSM / pkcs11 module:
```
p11tool --login --load-certificate=aws_iot_pk.crt --write --label=aws_iot_pk "pkcs11:token=default"
```

# Build the C-SDK demos:

Use a cmake command similar to the one listed below to build the desired demos:

```
cmake -B build2 -DBUILD_DEMOS=1 -DBUILD_TESTS=0 \
-DAWS_IOT_ENDPOINT="XXXXXXXXXXXXXX-ats.iot.XX-XXXX-X.amazonaws.com" \
-DCLIENT_CERT_PATH="pkcs11:token=default;object=aws_iot_pk" \
-DCLIENT_PRIVATE_KEY_PATH="pkcs11:token=default;object=aws_iot_pk?pin-value=0000" \
-DROOT_CA_CERT_PATH="pkcs11:token=System%20Trust;object=Amazon%20Root%20CA%201" \
-DBUILD_CLONE_SUBMODULES=0
```