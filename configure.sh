#!/bin/bash

# Get the directory where this bash script is located.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# Ask for user input and write the result to a variable named `answer`.
answer=true
prompt_user () {
    read -p "$1 " yn
    if [[ "$2" -eq 1 ]]; then
        # Return the answer as is.
        answer=$yn
    else
        # Treat as a yes or no prompt and return true or false respectively.
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
# Note: OpenSSL 1.1.0 or above is a requirement for running any TLS demos.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    echo "OpenSSL not found."
    if [ "$(uname)" == "Darwin" ]; then
        # Install Homebrew if not installed.
        # The advantage of Homebrew is compatibility with both Linux and Mac.
        if !([ -x "$(command -v brew)" ]); then
            echo "Installing Homebrew for OpenSSL installation..."
            /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"
        fi
        if !([ -x "$(command -v brew)" ]); then
            echo "Homebrew installation failed."
            exit 1
        else
            echo "Installing OpenSSL..."
            brew update
            brew install openssl@1.1
        fi
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        echo "Installing OpenSSL..."
        sudo apt-get install libssl-dev openssl -y
    else
        echo "$(uname) is not a supported platform."
    fi
fi

# Check if OpenSSL installation failed.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    # >&2 prints to stderr.
    >&2 echo "Error: OpenSSL installation failed. Please try to install it manually."
    >&2 echo "See https://wiki.openssl.org/index.php/Compilation_and_Installation for details."
    exit 1
fi

prompt_user "Would you like to install servers to run the MQTT and HTTP demos? [Y/n]" 0
install_servers=$answer

if [ "$install_servers" = true ]; then
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
            >&2 echo "Error: The command 'docker-compose' could not be found in this WSL distro."
            >&2 echo "Please use WSL 2, then activate the WSL integration in Docker Desktop settings."
            >&2 echo "See https://docs.docker.com/docker-for-windows/wsl/ for details."
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

    # Start the servers, making sure we have docker installed. :)
    if [ -x "$(command -v docker-compose)" ]; then
        # >&2 prints to stderr
        >&2 echo "Error: Docker failed to install. Please try installing Docker manually."
        exit 1
    else
        cd tools/local-servers && docker-compose stop && docker-compose up -d
    fi
else
    # Ask for hostname to use for MQTT and HTTP.
    prompt_user "What is the hostname of the MQTT broker?" 1
    broker_endpoint=$answer
    prompt_user "What is the hostname of the HTTP server?" 1
    http_server=$answer
fi

# Ask for configuration settings of the mutual auth demos.
prompt_user "Would you like to configure the mutual auth demos with your AWS IoT Core credentials? [Y/n]" 0
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
        # Look for the end marker.
        elif [[ $line = *-----END\ CERTIFICATE-----* ]]; then
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
        # Look for the end marker.
        elif [[ $line = *-----END\ RSA\ PRIVATE\ KEY-----* ]]; then
            break
        fi
    done
    echo "Writing certificate to file: $SCRIPT_DIR/demos/certificates/$client_key_filename"
    echo -e $client_key_contents > $SCRIPT_DIR/demos/certificates/$client_key_filename
fi

# Pass any options that the user has chosen to configure as CMake flags.
if [ "$install_servers" = true ]; then
    tls_cmake_flags="-DROOT_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/ca.crt 
                     -DBROKER_ENDPOINT=localhost 
                     -DSERVER_HOST=localhost"
fi
if [ "$configure_mutual_auth" = true ]; then
    mutual_auth_cmake_flags="-DAWS_IOT_ENDPOINT=$aws_iot_endpoint
                             -DAMAZON_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/AmazonRootCA1.crt
                             -DCLIENT_CERT_PATH=$SCRIPT_DIR/demos/certificates/$client_cert_filename
                             -DCLIENT_PRIVATE_KEY_PATH=$SCRIPT_DIR/demos/certificates/$client_key_filename"
fi

# Run CMake based on the configuration settings
cmake -S $SCRIPT_DIR \
# Shell parameter expansion is used for passing optional configuration parameters as CMake flags.
# If the variable to the left of :- is unset, the expression on the right is used.
# Otherwise, the value of the variable to the left is substituted.
${tls_cmake_flags:- -DBROKER_ENDPOINT="$broker_endpoint" -DSERVER_HOST="$http_server"} \
${mutual_auth_cmake_flags:-} \
-B $SCRIPT_DIR/build

exit 0
