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
    # First, try installing through apt-get.
    which apt-get
    if [[ $? -eq 0 ]]; then
        echo "Attempting to install OpenSSL through apt-get..."
        sudo apt-get update -y
        sudo apt-get install openssl libssl-dev -y
    fi
fi
# Ideally, yum would also be used for non-Debian Linux systems; however, yum does
# not support installation of OpenSSL 1.1.x out of the box.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    # Installing Homebrew on Linux will add it here: /home/linuxbrew/.linuxbrew
    # However, that directory will not be added to $PATH, so we need make the `brew`
    # command available for this bash script.
    if [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        test -d ~/.linuxbrew && eval $(~/.linuxbrew/bin/brew shellenv)
        test -d /home/linuxbrew/.linuxbrew && eval $(/home/linuxbrew/.linuxbrew/bin/brew shellenv)
    fi
    # The advantage of Homebrew is compatibility with several Linux and Mac distros.
    # Try installing Homebrew if not installed.
    if !([ -x "$(command -v brew)" ]); then
        echo "Installing Homebrew for OpenSSL installation..."
        # Install Homebrew dependencies.
        if ([ -x "$(command -v apt-get)" ]); then
            sudo apt-get install build-essential curl file git -y
        fi
        if ([ -x "$(command -v yum)" ]); then
            sudo yum -y groupinstall 'Development Tools'
            sudo yum -y install curl file git
            # Needed by Fedora 30 and up.
            sudo yum -y install libxcrypt-compat
        fi
        # Install Homebrew.
        /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"
        if [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
            # Make the `brew` command available for this bash script.
            test -d ~/.linuxbrew && eval $(~/.linuxbrew/bin/brew shellenv)
            test -d /home/linuxbrew/.linuxbrew && eval $(/home/linuxbrew/.linuxbrew/bin/brew shellenv)
        fi
    fi
    if !([ -x "$(command -v brew)" ]); then
        echo "Homebrew installation failed."
        exit 1
    else
        echo "Installing OpenSSL..."
        brew update
        brew install openssl@1.1
        openssl_root_dir=$(brew --prefix openssl@1.1)
    fi
fi

# Treat a missing OpenSSL package at this point as a fatal error.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    # >&2 prints to stderr.
    >&2 echo "Fatal: OpenSSL installation failed. Please try installing manually, then run this script again."
    >&2 echo "See https://wiki.openssl.org/index.php/Compilation_and_Installation for details."
    exit 1
fi

prompt_user "Install locally hosted servers to run the MQTT and HTTP demos? [Y/n]" 0
install_servers=$answer

if [ "$install_servers" = true ]; then
    # Install Docker if docker does not exist as a command.
    docker -v
    if [[ $? -ne 0 ]]; then
        if ! [ grep -q Microsoft /proc/version ]; then
            # This will only work in non-WSL distros.
            echo "Docker not found. Installing Docker..."
            curl -fsSL https://get.docker.com -o get-docker.sh
            sh get-docker.sh
        else
            # Docker cannot be installed straight to a WSL distro.
            # Instead, it must be installed on the Windows host machine.
            >&2 echo "Fatal: The command 'docker-compose' could not be found in this WSL distro."
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

    # Start the servers, making sure we have docker installed.
    docker -v
    if [[ $? -ne 0 ]]; then
        # >&2 prints to stderr.
        >&2 echo "Fatal: Docker failed to install. Please try installing manually, then run this script again."
        exit 1
    else
        cd $SCRIPT_DIR/tools/local-servers
        sudo docker-compose stop
        sudo docker-compose up -d
    fi
else
    # Ask for hostname to use for MQTT and HTTP.
    prompt_user "What is the hostname of the MQTT broker?" 1
    broker_endpoint=$answer
    prompt_user "What is the hostname of the HTTP server?" 1
    http_server=$answer
fi

# Ask for configuration settings of the mutual auth demos.
echo "AWS IoT Core is a managed cloud service that lets connected devices easily and securely interact with cloud applications and other devices."
echo "See https://aws.amazon.com/iot-core/ for details."
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
        # Ignore initial empty lines and white space before a beginning marker is inserted.
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
    # The -e allows us to write escape characters.
    echo -e $client_cert_contents > $SCRIPT_DIR/demos/certificates/$client_cert_filename

    # Because a key is multiline, parse until the end marker is reached.
    echo "Paste your AWS IoT Private Key:"
    client_key_contents=""
    found_begin=false
    while read line
    do
        # Ignore initial empty lines and white space before a beginning marker is inserted.
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
    tls_cmake_flags="-DROOT_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/ca.crt \
                     -DBROKER_ENDPOINT=localhost \ 
                     -DSERVER_HOST=localhost"
fi
if [ "$configure_mutual_auth" = true ]; then
    mutual_auth_cmake_flags="-DAWS_IOT_ENDPOINT=$aws_iot_endpoint \
                             -DAMAZON_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/AmazonRootCA1.crt \
                             -DCLIENT_CERT_PATH=$SCRIPT_DIR/demos/certificates/$client_cert_filename \
                             -DCLIENT_PRIVATE_KEY_PATH=$SCRIPT_DIR/demos/certificates/$client_key_filename"
fi
# Set the root directory for a Homebrew installation of OpenSSL.
# This is necessary for Mac and non-Debian systems.
if !([ -z "$openssl_root_dir" ]); then
    echo "Setting OPENSSL_ROOT_DIR system variable to path: $openssl_root_dir"
    export OPENSSL_ROOT_DIR=$openssl_root_dir
    openssl_cmake_flags="-DOPENSSL_ROOT_DIR=$openssl_root_dir \
                         -DOPENSSL_LIBRARIES=$openssl_root_dir/lib \
                         -DOPENSSL_INCLUDE_DIR=$openssl_root_dir/include"
fi

# Run CMake based on the configuration settings.
# Shell parameter expansion is used for passing optional configuration parameters as CMake flags.
# If the variable to the left of :- is unset, the expression on the right is used.
# Otherwise, the value of the variable to the left is substituted.
# Note: sudo permissions needed for the file(COPY ...) command.
sudo cmake -S $SCRIPT_DIR -B $SCRIPT_DIR/build \
${tls_cmake_flags:- -DBROKER_ENDPOINT="$broker_endpoint" -DSERVER_HOST="$http_server"} \
${mutual_auth_cmake_flags:-} \
${openssl_cmake_flags:-} \
;

exit 0
