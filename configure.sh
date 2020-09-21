#!/bin/bash

# Get the directory where this bash script is located.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# Default command line options.
BUILD=false
CONFIGFILE="$SCRIPT_DIR/config.yml"

# Parse command line options such as --option value.
POSITIONAL=()
while [[ $# -gt 0 ]]
do
    key="$1"
    case $key in
        -b|--build)
        BUILD="$2"
        shift
        shift
        ;;
        -c|--configfile)
        CONFIGFILE="$2"
        shift
        shift
        ;;
        *)
        # Save it in an array for later.
        POSITIONAL+=("$1")
        shift
        ;;
    esac
done
set -- "${POSITIONAL[@]}" # restore positional parameters

# Ask for user input and write the result to a variable named `answer`.
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

# Parse a pasted certificate and store the contents in the global: $cert.
parse_cert () {
    cert=""
    found_begin=false
    while read line
    do
        # Ignore initial empty lines and white space before a beginning marker is inserted.
        if [[ $line = "" ]]; then
            continue
        else
            cert+="${line}\r\n"
        fi
        # Look for the beginning marker.
        if [[ $found_begin = false ]]; then
            if [[ $cert = -----BEGIN\ CERTIFICATE-----* ]]; then
                found_begin=true
            else
                echo "Invalid certificate given. Certificates must start with:"
                echo "-----BEGIN CERTIFICATE-----"
                echo "Please try pasting your certificate again: "
                cert=""
                continue
            fi
        # Look for the end marker.
        elif [[ $line = *-----END\ CERTIFICATE-----* ]]; then
            break
        fi
    done
}

# Parse a pasted key and store the contents in the global: $key.
parse_key () {
    key=""
    found_begin=false
    while read line
    do
        # Ignore initial empty lines and white space before a beginning marker is inserted.
        if [[ $line = "" ]]; then
            continue
        else
            key+="${line}\r\n"
        fi
        # Look for the beginning marker.
        if [[ $found_begin = false ]]; then
            if [[ $key = -----BEGIN\ RSA\ PRIVATE\ KEY-----* ]]; then
                found_begin=true
            else
                echo "Invalid private key given. Private keys must start with:"
                echo "-----BEGIN RSA PRIVATE KEY-----"
                echo "Please try pasting your AWS IoT Private Key again: "
                key=""
                continue
            fi
        # Look for the end marker.
        elif [[ $line = *-----END\ RSA\ PRIVATE\ KEY-----* ]]; then
            break
        fi
    done
    # This clears the screen so as to remove the pasted key from the terminal.
    printf "\033c"
}

# Install any dependencies or packages required for C SDK.
# These include OpenSSL and CMake.
install_dependencies () {
    # Check if OpenSSL was already installed through Homebrew.
    # Note: Not needed for Mac as `brew` is automatically added to its $PATH.
    if [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        test -d ~/.linuxbrew && eval $(~/.linuxbrew/bin/brew shellenv)
        test -d /home/linuxbrew/.linuxbrew && eval $(/home/linuxbrew/.linuxbrew/bin/brew shellenv)
        brew list openssl@1.1 > /dev/null
        if [[ $? -eq 0 ]]; then
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

    # Treat a missing CMake package at this point as a fatal error.
    if !([ -x "$(command -v cmake)" ] && [[ $(cmake -version) = cmake\ version\ 3* ]]); then
        # >&2 prints to stderr.
        >&2 echo "Fatal: CMake installation failed. Please try installing it manually, then run this script again."
        >&2 echo "See https://cmake.org/install/ for details."
        exit 1
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

    # Treat a missing OpenSSL package at this point as a fatal error.
    if !([ -x "$(command -v openssl)" ] && [[ $(openssl version) = OpenSSL\ 1.1* ]]); then
        # >&2 prints to stderr.
        >&2 echo "Fatal: OpenSSL installation failed. Please try installing it manually, then run this script again."
        >&2 echo "See https://wiki.openssl.org/index.php/Compilation_and_Installation for details."
        exit 1
    fi
}

# If this script has been run before,
# a config.yml file will exist from which to load configurations.
# Note: This can only parse yml files that have each line as KEY: VALUE.
load_existing_configs=false
if [[ -f $CONFIGFILE ]]; then
    echo "Found a config file in $CONFIGFILE."
    if [[ "$CONFIGFILE" = "$SCRIPT_DIR/config.yml" ]]; then
        echo "This file most likely contains the configurations from the last time this script was run."
    fi
    prompt_user "Would you like to use configurations from this file? [Y/n]" 0
    load_existing_configs=$answer
    # Load the configurations into their respective variables.
    idx=0
    key=""
    value=""
    if [ $load_existing_configs = true ]; then
        while IFS=':' read -ra keyval; do
            for i in "${keyval[@]}"; do
                # Trim trailing and leading whitespace.
                i=$(echo $i | awk '{$1=$1};1')
                if (( $idx % 2 )); then
                    value="$i"
                    echo "Setting $key to $value."
                    # Set $key into a bash variable with its value being $value.
                    eval "$key"="$value"
                else
                    key="$i"
                fi
                ((idx++))
            done
        done < "$CONFIGFILE"
    fi
else
    touch $CONFIGFILE
fi

install_dependencies

if [[ $load_existing_configs = false ]] || [ -z "$run_servers" ]; then
    mkdir -p $SCRIPT_DIR/temp
    prompt_user "Run locally hosted servers for the MQTT and HTTP Client Demos? [Y/n]" 0
    run_servers=$answer

    echo "run_servers: $run_servers" >> "$CONFIGFILE"
fi

if [ "$run_servers" = true ]; then
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
    if [[ $load_existing_configs = false ]] || [ -z "$broker_endpoint" ]; then
        prompt_user "What is the hostname of the MQTT broker?" 1
        broker_endpoint=$answer

        echo "broker_endpoint: $broker_endpoint" >> "$CONFIGFILE"
    fi
    if [[ $load_existing_configs = false ]] || [ -z "$http_server" ]; then
        prompt_user "What is the hostname of the HTTP server?" 1
        http_server=$answer

        echo "http_server: $http_server" >> "$CONFIGFILE"
    fi
    if [[ $load_existing_configs = false ]] || [ -z "$root_ca_cert_path" ]; then
        echo "Paste the Root CA Certificate of the servers: "
        parse_cert
        root_ca_contents=$cert
        root_ca_cert_path="$SCRIPT_DIR/demos/certificates/root_ca.crt"
        echo "Writing certificate to file: $root_ca_cert_path"
        # The -e allows us to write escape characters.
        echo -e $root_ca_contents > $root_ca_cert_path

        echo "root_ca_cert_path: $root_ca_cert_path" >> "$CONFIGFILE"
    fi
fi

# Ask for configuration settings of the mutual auth demos.
echo "AWS IoT Core is a managed cloud service that lets connected devices easily and securely interact with cloud applications and other devices."
echo "See https://aws.amazon.com/iot-core/ for details."
if [[ $load_existing_configs = false ]] || [ -z "$aws_iot_endpoint" ] || \
                                           [ -z "$client_cert_path" ] || \
                                           [ -z "$client_key_path" ]; then
    prompt_user "Would you like to configure the mutual auth demos with your AWS IoT Core credentials? [Y/n]" 0
    configure_mutual_auth=$answer
fi

if [ "$configure_mutual_auth" = true ] ; then
    client_cert_filename="aws_iot_client.crt"
    client_key_filename="aws_iot_client.key"

    if [[ $load_existing_configs = false ]] || [ -z "$aws_iot_endpoint" ]; then
        # Ask for the AWS IoT Endpoint.
        prompt_user "Paste your AWS IoT Endpoint:" 1
        aws_iot_endpoint=$answer

        echo "aws_iot_endpoint: $aws_iot_endpoint" >> "$CONFIGFILE"
    fi

    if [[ $load_existing_configs = false ]] || [ -z "$client_cert_path" ]; then
        # Because a certificate is multiline, parse until the end marker is reached.
        echo "Paste your AWS IoT Client Certificate:"
        parse_cert
        client_cert_contents=$cert
        client_cert_path="$SCRIPT_DIR/demos/certificates/$client_cert_filename"
        echo "Writing certificate to file: $client_cert_path"
        # The -e allows us to write escape characters.
        echo -e $client_cert_contents > $client_cert_path

        echo "client_cert_path: $client_cert_path" >> "$CONFIGFILE"
    fi

    if [[ $load_existing_configs = false ]] || [ -z "$client_key_path" ]; then
        # Because a key is multiline, parse until the end marker is reached.
        echo "Paste your AWS IoT Private Key:"
        parse_key
        client_key_contents=$key
        client_key_path="$SCRIPT_DIR/demos/certificates/$client_key_filename"
        echo "Writing private key to file: $client_key_path"
        echo -e $client_key_contents > $client_key_path

        echo "client_key_path: $client_key_path" >> "$CONFIGFILE"
    fi

    echo "AWS IoT Core credentials have been set."
fi

# Pass any options that the user has chosen to configure as CMake flags.
if [ "$run_servers" = true ]; then
    hostname_cmake_flags="-DROOT_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/ca.crt \
                          -DBROKER_ENDPOINT=localhost \ 
                          -DSERVER_HOST=localhost"
fi
if [ "$configure_mutual_auth" = true ]; then
    mutual_auth_cmake_flags="-DAWS_IOT_ENDPOINT=$aws_iot_endpoint \
                             -DAMAZON_CA_CERT_PATH=$SCRIPT_DIR/demos/certificates/AmazonRootCA1.crt \
                             -DCLIENT_CERT_PATH=$client_cert_path \
                             -DCLIENT_PRIVATE_KEY_PATH=$client_key_path"
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
sudo cmake .. -B$SCRIPT_DIR/build \
${hostname_cmake_flags:- -DBROKER_ENDPOINT="$broker_endpoint" -DSERVER_HOST="$http_server" -DROOT_CA_CERT_PATH="$root_ca_cert_path"} \
${mutual_auth_cmake_flags:-} \
${openssl_cmake_flags:-} \
;

# Automatically build demos if the --build parameter was passed.
if !([[ $BUILD = false ]]); then
    make -j4 -C $SCRIPT_DIR/build
    echo "Demo executables built."
    echo "They can be found in $SCRIPT_DIR/build/bin."
fi

# Cleanup.
rm -rf $SCRIPT_DIR/temp

exit 0
