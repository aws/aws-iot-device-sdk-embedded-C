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

# Install Homebrew if not installed.
# Homebrew is compatible with Mac and several Linux distros.
install_brew () {
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
}

# If this script has been run before,
# a configuration.yml file will exist from which to load configurations.
echo "This script has been run before."
prompt_user "Would you like to use the same configurations from last time? [Y/n]" 0

# Check if OpenSSL was already installed through Homebrew.
# Note: Not needed for Mac as `brew` is automatically added to its $PATH.
if [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    test -d ~/.linuxbrew && eval $(~/.linuxbrew/bin/brew shellenv)
    test -d /home/linuxbrew/.linuxbrew && eval $(/home/linuxbrew/.linuxbrew/bin/brew shellenv)
fi

# Install OpenSSL if it is not installed or the version is less than 1.1.x.
# Note: OpenSSL 1.1.0 or above is a requirement for running any TLS demos.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    echo "OpenSSL not found."
    # Try installing through apt-get.
    if ([ -x "$(command -v apt-get)" ]); then
        echo "Attempting to install OpenSSL through apt-get..."
        sudo apt-get update -y
        sudo apt-get install --only-upgrade openssl libssl-dev -y
        sudo apt-get install openssl libssl-dev -y
    fi
    # Unfortunately, yum does not have packages for installing OpenSSL 1.1.x.
fi

if !([ -x "$(command -v cmake)" ] && [[ $(cmake -version) = cmake\ version\ 3* ]]); then
    echo "CMake not found."
    # Try installing through apt-get.
    if ([ -x "$(command -v apt-get)" ]); then
        echo "Attempting to install CMake through apt-get..."
        sudo apt-get update -y
        sudo apt-get install --only-upgrade cmake -y
        sudo apt-get install cmake -y
    fi
    # Try installing through yum.
    if ([ -x "$(command -v yum)" ]); then
        echo "Attempting to install CMake through yum..."
        sudo yum -y install cmake
        sudo yum -y update cmake
    fi
fi

if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    install_brew
    if !([ -x "$(command -v brew)" ]); then
        echo "Homebrew installation failed."
        exit 1
    else
        echo "Attempting to install OpenSSL through Homebrew..."
        brew install openssl@1.1
        openssl_root_dir=$(brew --prefix openssl@1.1)
    fi
fi

if !([ -x "$(command -v cmake)" ] && [[ $(cmake -version) = cmake\ version\ 3* ]]); then
    install_brew
    if !([ -x "$(command -v brew)" ]); then
        echo "Homebrew installation failed."
        exit 1
    else
        echo "Attempting to install CMake through Homebrew..."
        brew install cmake
    fi
fi

# This array will contain configurations to save into a yaml file later on.
configs=("wtf $wtf")

# Iterate the loop to read and print each array element
for value in "${configs[@]}"
do
    set -- $value
    echo $1 and $2
done

# Treat a missing OpenSSL package at this point as a fatal error.
if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
    # >&2 prints to stderr.
    >&2 echo "Fatal: OpenSSL installation failed. Please try installing manually, then run this script again."
    >&2 echo "See https://wiki.openssl.org/index.php/Compilation_and_Installation for details."
    exit 1
fi

mkdir -p $SCRIPT_DIR/temp
prompt_user "Run locally hosted servers for the MQTT and HTTP Client Demos? [Y/n]" 0
install_servers=$answer

if [ "$install_servers" = true ]; then
    # Install Docker if `docker` does not exist as a command.
    docker -v
    if [[ $? -ne 0 ]]; then
        echo "Docker not found. Installing Docker..."
        curl -fsSL https://get.docker.com -o $SCRIPT_DIR/temp/get-docker.sh
        sh $SCRIPT_DIR/temp/get-docker.sh
        rm $SCRIPT_DIR/temp/get-docker.sh
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
    # Ask for hostname to use for MQTT and HTTP only if servers haven't been configured to run.
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
    echo "Valid certificate pasted."
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
    # This clears the screen so as to remove the pasted certificate from the terminal.
    printf "\033c"
    echo "Valid private key pasted."
    echo "Writing private key to file: $SCRIPT_DIR/demos/certificates/$client_key_filename"
    echo -e $client_key_contents > $SCRIPT_DIR/demos/certificates/$client_key_filename
    echo "AWS IoT Core Credentials have been set."
fi

# Pass any options that the user has chosen to configure as CMake flags.
if [ "$install_servers" = true ]; then
    hostname_cmake_flags="-DROOT_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/ca.crt \
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
${hostname_cmake_flags:- -DBROKER_ENDPOINT="$broker_endpoint" -DSERVER_HOST="$http_server"} \
${mutual_auth_cmake_flags:-} \
${openssl_cmake_flags:-} \
;

rm -rf $SCRIPT_DIR/temp

exit 0
