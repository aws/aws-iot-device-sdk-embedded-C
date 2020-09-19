#!/bin/bash

answer=true
prompt_user () {
    read -p "$1 " yn
    case $yn in
        [Yy]* ) answer=true;;
        [Nn]* ) answer=false;;
        * ) echo "Please answer yes or no."; prompt_user $1;;
    esac
}

# If this script has been run before,
# a configuration.yml file will exist from which to load configurations.

# Install OpenSSL if it is not installed or the version is less than 1.1.x.
openssl_version=$(openssl version)
if !([ -x "$(command -v openssl)" ] && [[ $openssl_version = OpenSSL\ 1.1* ]]); then
    sudo apt-get install libssl-dev
fi

prompt_user "Would you like to install servers to run the MQTT and HTTP demos? [y/n]"
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
            install_servers=false
        fi
    fi
fi

if [ "$install_servers" = true ] ; then
    # Generate certificates and keys for the TLS demos.
    echo "Generating certificates with OpenSSL..."
    # Generate CA key and certificate. Provide the Subject field information as appropriate.
    openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 \
    -keyout demos/certificates/ca.key -out demos/certificates/ca.crt \
    -subj "/C=CA/ST=CA/L=CA/O=CA/CN=localhost" # The subject field is mocked.
    # Generate server key and certificate.
    openssl req -nodes -sha256 -new \
    -keyout demos/certificates/key.pem -out demos/certificates/server.csr \
    -subj "/C=SV/ST=SV/L=SV/O=SV/CN=localhost" # The subject field is mocked.
    # Sign with the CA cert.
    openssl x509 -req -sha256 -in demos/certificates/server.csr -CA demos/certificates/ca.crt \
    -CAkey demos/certificates/ca.key -CAcreateserial -out demos/certificates/cert.pem -days 365
    # Servers can now use certificates to make a TLS connection.
    echo "Certificates generated"
    # Start the servers. :)
    cd tools/local-servers && docker-compose stop && docker-compose start
else
    # Prompt for hostnames of the server and port
    echo "No install servers"
fi

# Ask for configuration settings of the mutual auth demos.
prompt_user "Would you like to configure the mutual auth demos with your AWS IoT Core credentials? [y/n]"
echo $answer

#mkdir -p build && cd build
#cmake ..
