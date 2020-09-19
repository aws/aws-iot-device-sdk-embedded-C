#!/bin/bash

# Get the directory where this bash script is located.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# Ask for user input and write the input to a variable named `answer`.
answer=true
prompt_user () {
    read -p "$1 " yn
    if [[ "$2" -eq 1 ]]; then
        # Return the answer as is.
        answer=$yn
    else
        # Treat as a yes or no prompt and return true or false.
        case $yn in
            [Yy]* ) answer=true;;
            [Nn]* ) answer=false;;
            * ) echo "Please answer yes or no."; prompt_user "$1" "$2";;
        esac
    fi
}

# If this script has been run before,
# a configuration.yml file will exist from which to load configurations.

# Install OpenSSL if it is not installed or the version is less than 1.1.x.
openssl_version=$(openssl version)
if !([ -x "$(command -v openssl)" ] && [[ $openssl_version = OpenSSL\ 1.1* ]]); then
    sudo apt-get install libssl-dev
fi

prompt_user "Would you like to install servers to run the MQTT and HTTP demos? [y/n]" 0
install_servers=$answer

if [ "$install_servers" = true ] ; then
    # Install Docker if docker-compose does not exist as a command.
    if ! [ -x "$(command -v docker-compose)" ]; then
        if ! [ grep -q Microsoft /proc/version ]; then
            # This will only work in non-WSL distros.
            echo "Docker not found. Installing Docker..."
            curl -fsSL https://get.docker.com -o get-docker.sh
            sh get-docker.sh
        else
            # Docker cannot be installed straight to a WSL distro.
            # Instead, it must be installed on the Windows host machine.
            echo "The command 'docker-compose' could not be found in this WSL distro."
            echo "Please use WSL 2, then activate the WSL integration in Docker Desktop settings."
            echo "See https://docs.docker.com/docker-for-windows/wsl/ for details."
            # Servers need docker-compose to be installed.
            exit 1
        fi
    fi

    # Generate certificates and keys for the TLS demos.
    echo "Generating server certificates with OpenSSL..."
    # Generate CA key and certificate. Provide the Subject field information as appropriate.
    openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 \
    -keyout $SCRIPT_DIR/demos/certificates/ca.key -out $SCRIPT_DIR/demos/certificates/ca.crt \
    -subj "/C=CA/ST=CA/L=CA/O=CA/CN=localhost" # The subject field is mocked.
    # Generate server key and certificate.
    openssl req -nodes -sha256 -new \
    -keyout $SCRIPT_DIR/demos/certificates/key.pem -out $SCRIPT_DIR/demos/certificates/server.csr \
    -subj "/C=SV/ST=SV/L=SV/O=SV/CN=localhost" # The subject field is mocked.
    # Sign with the CA cert.
    openssl x509 -req -sha256 -in $SCRIPT_DIR/demos/certificates/server.csr -CA $SCRIPT_DIR/demos/certificates/ca.crt \
    -CAkey $SCRIPT_DIR/demos/certificates/ca.key -CAcreateserial -out $SCRIPT_DIR/demos/certificates/cert.pem -days 365
    # Servers can now use certificates to make a TLS connection.
    echo "Server certificates have been generated."

    # Start the servers. :)
    cd tools/local-servers && docker-compose stop && docker-compose up -d
else
    # Ask for hostname to use for MQTT and HTTP.
    prompt_user "What is the hostname of the MQTT broker?" 1
    echo $answer
    prompt_user "What is the hostname of the HTTP server?" 1
    echo $answer
fi

# Ask for configuration settings of the mutual auth demos.
prompt_user "Would you like to configure the mutual auth demos with your AWS IoT Core credentials? [y/n]" 0
configure_mutual_auth=$answer

client_cert_filename="aws_iot_client.crt"
client_key_filename="aws_iot_client.key"

if [ "$configure_mutual_auth" = true ] ; then
    # Ask for the AWS IoT Endpoint.
    prompt_user "Paste your AWS IoT Endpoint:" 1
    aws_iot_endpoint=$answer

    # Because a certificate is multiline, parse until the end marker is reached.
    echo "Paste your AWS IoT Client Certificate:"
    client_cert_contents=""
    found_begin=false
    while read line
    do
        # Ignore empty lines and white space.
        if [[ $line = "" ]]; then
            continue
        else
            client_cert_contents+="${line}\r\n"
        fi
        # Look for the beginning marker.
        if [[ $found_begin = false ]]; then
            if [[ $client_cert_contents = -----BEGIN\ CERTIFICATE-----* ]]; then
                found_begin=true
            else
                echo "Invalid certificate given. Certificates must start with:"
                echo "-----BEGIN CERTIFICATE-----"
                echo "Please try pasting your AWS IoT Client Certificate again: "
                client_cert_contents=""
                continue
            fi
        fi
        # Look for the end marker.
        if [[ $line = *-----END\ CERTIFICATE-----* ]]; then
            break
        fi
    done
    echo "Writing certificate to file: $SCRIPT_DIR/demos/certificates/$client_cert_filename"
    echo -e $client_cert_contents > $SCRIPT_DIR/demos/certificates/$client_cert_filename

    # Because a key is multiline, parse until the end marker is reached.
    echo "Paste your AWS IoT Private Key:"
    client_key_contents=""
    found_begin=false
    while read line
    do
        # Ignore empty lines and white space.
        if [[ $line = "" ]]; then
            continue
        else
            client_key_contents+="${line}\r\n"
        fi
        # Look for the beginning marker.
        if [[ $found_begin = false ]]; then
            if [[ $client_key_contents = -----BEGIN\ RSA\ PRIVATE\ KEY-----* ]]; then
                found_begin=true
            else
                echo "Invalid private key given. Private keys must start with:"
                echo "-----BEGIN RSA PRIVATE KEY-----"
                echo "Please try pasting your AWS IoT Private Key again: "
                client_key_contents=""
                continue
            fi
        fi
        # Look for the end marker.
        if [[ $line = *-----END\ RSA\ PRIVATE\ KEY-----* ]]; then
            break
        fi
    done
    echo "Writing certificate to file: $SCRIPT_DIR/demos/certificates/$client_key_filename"
    echo -e $client_key_contents > $SCRIPT_DIR/demos/certificates/$client_key_filename
fi

cmake -S $SCRIPT_DIR -B $SCRIPT_DIR/build \
-DAWS_IOT_ENDPOINT="$aws_iot_endpoint" \
-DROOT_CA_CERT_PATH="$SCRIPT_DIR/demos/certificates/ca.crt" \
-DAMAZON_CA_CERT_PATH="$SCRIPT_DIR/demos/certificates/AmazonRootCA1.crt" \
-DCLIENT_CERT_PATH="$SCRIPT_DIR/demos/certificates/$client_cert_filename" \
-DCLIENT_PRIVATE_KEY_PATH="$SCRIPT_DIR/demos/certificates/$client_key_filename"

exit 0
