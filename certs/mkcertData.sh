#!/bin/bash
WD=$(cd `dirname $0` && pwd)

CERTDATA_FILE=certData.c

#1 rootCA

tee ${CERTDATA_FILE} << __EOF__

/* root CA certificate file */

const unsigned char root_ca_pem[] =
__EOF__

while IFS='' read -r line
do
	echo '\t"'"$line"'\\r\\n"' >> ${CERTDATA_FILE}
done < "$1"

echo ';' >> ${CERTDATA_FILE}

tee -a ${CERTDATA_FILE} << __EOF__
const int rootCaLen = sizeof(root_ca_pem);
__EOF__

#2 cert.pem

tee -a ${CERTDATA_FILE} << __EOF__

/* cert.pem certificate file */

const unsigned char client_cert_pem[] =
__EOF__

while IFS='' read -r line
do
	echo '\t"'"$line"'\\r\\n"' >> ${CERTDATA_FILE}
done < "$2"

echo ';' >> ${CERTDATA_FILE}

tee -a ${CERTDATA_FILE} << __EOF__
const int clientCertLen = sizeof(client_cert_pem);
__EOF__

#3 privateKey.pem

tee -a ${CERTDATA_FILE} << __EOF__

/* privateKey.pem certificate file */

const unsigned char client_private_key_pem[] =
__EOF__

while IFS='' read -r line
do
	echo '\t"'"$line"'\\r\\n"' >> ${CERTDATA_FILE}
done < "$3"

echo ';' >> ${CERTDATA_FILE}

tee -a ${CERTDATA_FILE} << __EOF__
const int clientPrivateKeyLen = sizeof(client_private_key_pem);
__EOF__
