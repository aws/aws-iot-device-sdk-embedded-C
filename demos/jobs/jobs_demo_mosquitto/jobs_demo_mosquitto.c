/*
 * AWS IoT Device SDK for Embedded C 202412.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/*
 * This demonstration downloads files from URLs present in job documents
 * received from the AWS IoT Jobs service. It shows the use of the jobs
 * library with the Mosquitto client MQTT library for communicating with the
 * AWS IoT Jobs service.  More details are available in the usage function
 * in this file.  Note: This demo focuses on use of the jobs library;
 * a thorough explanation of libmosquitto is beyond the scope of the demo.
 */

/* C standard includes. */
#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* POSIX includes. */
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <err.h>
#include <getopt.h>

#include <mosquitto.h>
#if ( LIBMOSQUITTO_VERSION_NUMBER < 1004010 )
    #error Please use libmosquitto at version 1.4.10 or higher.
#endif

#include "demo_config.h"
#include "jobs.h"
#include "core_json.h"

/*-----------------------------------------------------------*/

/**
 * @brief MQTT server port number.
 *
 * AWS IoT Core uses this port for MQTT over TLS.
 */
#define DEFAULT_MQTT_PORT       ( 8883 )

/**
 * @brief Certificate Authority Directory.
 *
 * Debian and Ubuntu use this directory for CA certificates.
 */
#define DEFAULT_CA_DIRECTORY    "/etc/ssl/certs"

/**
 * @brief ALPN (Application-Layer Protocol Negotiation) name for AWS IoT MQTT.
 */
#define ALPN_NAME               "x-amzn-mqtt-ca"


/*-----------------------------------------------------------*/

/**
 * @brief Describe program usage on stderr.
 *
 * @param[in] programName the value of argv[0]
 */
static void usage( const char * programName )
{
    fprintf( stderr,
             "\nThis demonstration downloads files from URLs received via AWS IoT Jobs.\n"
             "(See https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html for an introduction.)\n"
             "\nCreating a job may be done with the AWS console, or the aws cli, e.g.,\n"
             "$ aws iot create-job --job-id t12 --targets arn:aws:iot:us-east-1:1234567890:thing/device1 \\\n"
             "  --document '{\"url\":\"https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.8.5.tar.xz\"}'\n"
             "\nTo execute the job, on the target device run the demo program with the device's credentials, e.g.,\n"
             "$ %s -n device1 -h abcdefg123.iot.us-east-1.amazonaws.com \\\n"
             "  --certfile bbaf123456-certificate.pem.crt --keyfile bbaf123456-private.pem.key\n"
             "\nTo exit the program, type Control-C, or send a SIGTERM signal.\n",
             programName );
    fprintf( stderr,
             "\nOutput should look like the following:\n"
             "Connecting to abcdefg123.iot.us-east-1.amazonaws.com, port 8883.\n"
             "Client device1 sending CONNECT\n"
             "Client device1 received CONNACK\n"
             "Client device1 sending SUBSCRIBE (Mid: 1, Topic: $aws/things/device1/jobs/start-next/accepted, QoS: 1)\n"
             "Client device1 received SUBACK\n"
             "[...]\n"
             "starting job id: t12\n"
             "sending first update\n" );
    fprintf( stderr,
             "\nIf the output does not show a successful connection, check in the AWS console\n"
             "that the client certificate is associated with the target thing and is activated.\n"
             "Also check that the Amazon Root CA certificates are in your system's trust store.\n"
             "Note, you can provide a CA certificate file directly as a command-line argument.\n" );
    fprintf( stderr,
             "\nThis demonstration exits on most error conditions.  One way to retry while avoiding\n"
             "throttling due to excessive reconnects is to periodically relaunch from cron(8).\n"
             "Given a shell script wrapper with the necessary arguments called download, the following\n"
             "line in /etc/crontab would start the downloader unless it is already running.\n"
             "This tries every 3 minutes, with an additional random delay up to 2 minutes.\n\n"
             "*/3 * * * *  root  exec 9> /tmp/lock && flock -n 9 && sleep $((RANDOM %% 120)) && download\n"
             );
    fprintf( stderr,
             "\nusage: %s "
             "[-o] -n name -h host [-p port] {--cafile file | --capath dir} --certfile file --keyfile file [--pollinv seconds] [--updateinv seconds]\n"
             "\n"
             "-o : run once, exit after the first job is finished.\n"
             "-n : thing name\n"
             "-h : mqtt host to connect to.\n"
             "-p : network port to connect to. Defaults to %d.\n",
             programName, DEFAULT_MQTT_PORT );
    fprintf( stderr,
             "--cafile    : path to a file containing trusted CA certificates to enable encrypted\n"
             "              certificate based communication.\n"
             "--capath    : path to a directory containing trusted CA certificates to enable encrypted\n"
             "              communication.  Defaults to %s.\n"
             "--certfile  : client certificate for authentication in PEM format.\n"
             "--keyfile   : client private key for authentication in PEM format.\n",
             DEFAULT_CA_DIRECTORY );
    fprintf( stderr,
             "--pollinv   : after this many idle seconds, request a job.\n"
             "              Without this option and a positive value, no polling is done.\n"
             "--updateinv : after this many seconds running a job, resend the current status to the jobs service.\n"
             "              Without this option and a positive value, status is not resent.\n\n"
             );
}

/*-----------------------------------------------------------*/

/**
 * @brief The several states of execution.
 */
typedef enum
{
    None = 0, /* no current job */
    Ready,    /* job document received and parsed */
    Running,  /* download in progress */
    Cancel,   /* cancel due to failed update */
} runStatus_t;

/**
 * @brief All runtime parameters and state.
 */
typedef struct
{
    /* thing name */
    char * name;
    size_t nameLength;
    /* connection parameters */
    char * host;
    uint16_t port;
    char * cafile;
    char * capath;
    char * certfile;
    char * keyfile;
    uint32_t pollinv;   /* 0 (default) disables polling for new jobs */
    uint32_t updateinv; /* 0 (default) disables periodic resending of status */
    /* flags */
    bool runOnce;
    /* callback-populated values */
    int connectError;
    int subscribeQOS;
    /* mosquitto library handle */
    struct mosquitto * m;
    /* job parameters received via MQTT */
    char * jobid;
    size_t jobidLength;
    char * url;
    size_t urlLength;
    /* internal state tracking */
    runStatus_t runStatus;
    char * report;
    time_t lastPrompt;
    time_t lastUpdate;
    bool forcePrompt;
    bool forceUpdate;
    pid_t child;
} handle_t;

/*-----------------------------------------------------------*/

/**
 * @brief Populate a handle with default values.
 *
 * @param[in] p runtime state handle
 */
void initHandle( handle_t * p );

/**
 * @brief Validate the values within a handle.
 *
 * @param[in] h runtime state handle
 *
 * @return true if necessary arguments are present and valid;
 * false otherwise
 */
static bool requiredArgs( handle_t * h );

/**
 * @brief Populate a handle from command line arguments.
 *
 * @param[in] h runtime state handle
 * @param[in] argc count of arguments
 * @param[in] argv array of arguments
 *
 * @return false if there is an unrecognized switch;
 * true otherwise
 */
static bool parseArgs( handle_t * h,
                       int argc,
                       char * argv[] );

/**
 * @brief The libmosquitto callback for connection result.
 *
 * @param[in] m unused
 * @param[in] p runtime state handle
 * @param[in] rc connection result code
 */
static void on_connect( struct mosquitto * m,
                        void * p,
                        int rc );

/**
 * @brief Connect to AWS IoT Core MQTT broker.
 *
 * @param[in] h runtime state handle
 *
 * @return true if a connection is established;
 * false otherwise
 */
static bool connect( handle_t * h );

/**
 * @brief Disconnect from AWS IoT Core MQTT broker.
 *
 * @param[in] h runtime state handle
 */
static void closeConnection( handle_t * h );

/**
 * @brief The libmosquitto callback for subscription result.
 *
 * @param[in] m unused
 * @param[in] p runtime state handle
 * @param[in] mid unused
 * @param[in] qos_count count of granted subscriptions
 * @param[in] granted_qos the granted QOS subscription values
 */
static void on_subscribe( struct mosquitto * m,
                          void * p,
                          int mid,
                          int qos_count,
                          const int * granted_qos );

/**
 * @brief Subscribe to a Jobs topic.
 *
 * @param[in] h runtime state handle
 * @param[in] api the desired Jobs topic
 *
 * @return true if the broker granted the subscription;
 * false otherwise
 */
static bool subscribe( handle_t * h,
                       JobsTopic_t api );

/**
 * @brief Publish a status update for a job ID to the Jobs service.
 *
 * @param[in] h runtime state handle
 * @param[in] jobid the job ID
 * @param[in] jobidLength size of the job ID string
 * @param[in] report body of the update
 *
 * @return true if libmosquitto accepted the publish message;
 * false otherwise
 *
 * @note This does not call mosquitto_loop(); it expects main() to do so.
 */
static bool sendUpdate( handle_t * h,
                        char * jobid,
                        size_t jobidLength,
                        char * report );

/**
 * @brief Read job ID and URL from a JSON job document.
 *
 * @param[in] h runtime state handle
 * @param[in] message an MQTT publish message
 *
 * @return true if values were found and copied to the handle;
 * false otherwise
 */
static bool parseJob( handle_t * h,
                      const struct mosquitto_message * message );

/**
 * @brief The libmosquitto callback for a received publish message.
 *
 * @param[in] m unused
 * @param[in] p runtime state handle
 * @param[in] message an MQTT publish message
 *
 * This checks if a message corresponds to a Jobs API, and transitions
 * runtime state based on the API and current state.
 */
void on_message( struct mosquitto * m,
                 void * p,
                 const struct mosquitto_message * message );

/**
 * @brief Publish a request to the Jobs service to describe the next job.
 *
 * @param[in] h runtime state handle
 *
 * @return true if libmosquitto accepted the publish message;
 * false otherwise
 *
 * @note This does not call mosquitto_loop(); it expects main() to do so.
 */
static bool sendDescribeNext( handle_t * h );

/**
 * @brief Checks status of the download process.
 *
 * @param[in] h runtime state handle
 */
static void checkChild( handle_t * h );

/**
 * @brief Launch a download process.
 *
 * @param[in] h runtime state handle
 *
 * @return true if fork() succeeded;
 * false otherwise
 */
static bool download( handle_t * h );

/**
 * @brief Kill a download process.
 *
 * @param[in] h runtime state handle
 */
static void cancelDownload( handle_t * h );

/**
 * @brief The libmosquitto callback for log messages.
 *
 * @param[in] m unused
 * @param[in] p unused
 * @param[in] level unused
 * @param[in] log the message to print
 */
static void on_log( struct mosquitto * m,
                    void * p,
                    int level,
                    const char * log );

/**
 * @brief Generic signal handler.
 *
 * @param[in] signal the caught signal value
 */
static void catch( int signal );

/**
 * @brief Setup signal handling and libmosquitto.
 *
 * @param[in] h runtime state handle
 *
 * @return false if a step failed;
 * true otherwise
 */
static bool setup( handle_t * h );

/**
 * @brief Disconnect and clean up.
 *
 * @param[in] x unused
 * @param[in] p runtime state handle
 */
static void teardown( int x,
                      void * p );

/**
 * @brief Log an informational message.
 */
#define info    warnx

/**
 * @brief Format a JSON status message.
 *
 * @param[in] x one of "IN_PROGRESS", "SUCCEEDED", or "FAILED"
 */
#define makeReport_( x )    "{\"status\":\"" x "\"}"

/*-----------------------------------------------------------*/

void initHandle( handle_t * p )
{
    assert( p != NULL );

    handle_t h = { 0 };

    #ifdef AWS_IOT_ENDPOINT
        h.host = AWS_IOT_ENDPOINT;
    #endif

    #ifdef CLIENT_CERT_PATH
        h.certfile = CLIENT_CERT_PATH;
    #endif

    #ifdef CLIENT_PRIVATE_KEY_PATH
        h.keyfile = CLIENT_PRIVATE_KEY_PATH;
    #endif

    #ifdef ROOT_CA_CERT_PATH
        h.cafile = ROOT_CA_CERT_PATH;
    #else
        h.capath = DEFAULT_CA_DIRECTORY;
    #endif

    h.port = DEFAULT_MQTT_PORT;

    h.runOnce = false;

    /* initialize to -1, set by on_connect() to 0 or greater */
    h.connectError = -1;
    /* initialize to -1, set by on_subscribe() to 0 or greater */
    h.subscribeQOS = -1;

    *p = h;
}

/*-----------------------------------------------------------*/

static bool requiredArgs( handle_t * h )
{
    bool ret = true;
    struct stat s;

    assert( h != NULL );

#define checkString( x )                               \
    if( ( h->x == NULL ) || ( h->x[ 0 ] == '\0' ) )    \
    {                                                  \
        ret = false;                                   \
        warnx( "%s argument must not be empty", # x ); \
    }

    checkString( name );
    checkString( host );
    checkString( certfile );
    checkString( keyfile );

    if( h->nameLength > JOBS_THINGNAME_MAX_LENGTH )
    {
        ret = false;
        warnx( "name length must not exceed %d", JOBS_THINGNAME_MAX_LENGTH );
    }

#define checkPath( x )                                                            \
    if( ( h->x != NULL ) && ( h->x[ 0 ] != '\0' ) && ( stat( h->x, &s ) == -1 ) ) \
    {                                                                             \
        ret = false;                                                              \
        warn( "cannot access '%s'", h->x );                                       \
        h->x = NULL;                                                              \
    }

    checkPath( certfile );
    checkPath( keyfile );
    checkPath( cafile );

    checkPath( capath );

    /* use value in struct stat s from last check */
    if( ( h->capath != NULL ) && ( h->capath[ 0 ] != '\0' ) && ( !S_ISDIR( s.st_mode ) ) )
    {
        ret = false;
        warnx( "not a directory: %s", h->capath );
    }

    return ret;
}

/*-----------------------------------------------------------*/

static bool parseArgs( handle_t * h,
                       int argc,
                       char * argv[] )
{
    bool ret = true;

    assert( h != NULL );

    if( argc == 1 )
    {
        ret = false;
        usage( argv[ 0 ] );
    }

    while( ret == true )
    {
        int c, option_index = 0;
        long x;
        static struct option long_options[] =
        {
            { "once",      no_argument,       NULL, 'o' },
            { "name",      required_argument, NULL, 'n' },
            { "host",      required_argument, NULL, 'h' },
            { "port",      required_argument, NULL, 'p' },
            { "cafile",    required_argument, NULL, 'f' },
            { "capath",    required_argument, NULL, 'd' },
            { "certfile",  required_argument, NULL, 'c' },
            { "keyfile",   required_argument, NULL, 'k' },
            { "pollinv",   required_argument, NULL, 'P' },
            { "updateinv", required_argument, NULL, 'u' },
            { "help",      no_argument,       NULL, '?' },
            { NULL,        0,                 NULL, 0   }
        };

        c = getopt_long( argc, argv, "on:h:p:P:u:f:d:c:k:?",
                         long_options, &option_index );

        if( c == -1 )
        {
            break;
        }

        switch( c )
        {
            case 'o':
                h->runOnce = true;
                break;

            case 'n':
                h->name = optarg;
                h->nameLength = strlen( optarg );
                break;

            case 'h':
                h->host = optarg;
                break;

#define optargToInt( element, min, max )                \
    x = strtol( optarg, NULL, 0 );                      \
                                                        \
    if( ( x > min ) && ( x <= max ) )                   \
    {                                                   \
        h->element = x;                                 \
    }                                                   \
    else                                                \
    {                                                   \
        ret = false;                                    \
        warnx( "bad %s value: %s", # element, optarg ); \
    }

            case 'p':
                optargToInt( port, 0, 0xFFFF );
                break;

            case 'P':
                optargToInt( pollinv, 0, INTERVAL_MAX );
                break;

            case 'u':
                optargToInt( updateinv, 0, INTERVAL_MAX );
                break;

            case 'f':
                h->cafile = optarg;
                h->capath = NULL;
                break;

            case 'd':
                h->capath = optarg;
                break;

            case 'c':
                h->certfile = optarg;
                break;

            case 'k':
                h->keyfile = optarg;
                break;

            case '?':
            default:
                ret = false;
                usage( argv[ 0 ] );
        }
    }

    if( optind < argc )
    {
        ret = false;
        usage( argv[ 0 ] );
    }

    if( ret == true )
    {
        ret = requiredArgs( h );
    }

    return ret;
}

/*-----------------------------------------------------------*/

static void on_connect( struct mosquitto * m,
                        void * p,
                        int rc )
{
    handle_t * h = p;

    assert( h != NULL );

    h->connectError = rc;
}

/*-----------------------------------------------------------*/

static bool connect( handle_t * h )
{
    int ret = MOSQ_ERR_SUCCESS;
    size_t i;

    assert( h != NULL );
    assert( h->m != NULL );
    assert( h->connectError == -1 );

    if( h->port == 443 )
    {
        #if ( LIBMOSQUITTO_VERSION_NUMBER >= 1006000 )
            ret = mosquitto_string_option( h->m, MOSQ_OPT_TLS_ALPN, ALPN_NAME );
        #else
            warnx( "ALPN (port 443) is not supported by libmosquitto before version 1.6" );
            ret = MOSQ_ERR_INVAL;
        #endif
    }

    if( ret == MOSQ_ERR_SUCCESS )
    {
        ret = mosquitto_tls_set( h->m, h->cafile, h->capath, h->certfile, h->keyfile, NULL );
    }

    if( ret == MOSQ_ERR_SUCCESS )
    {
        info( "Connecting to %s, port %d.", h->host, h->port );
        ret = mosquitto_connect( h->m, h->host, h->port, MQTT_KEEP_ALIVE );
    }

    /* expect the on_connect() callback to update h->connectError */
    for( i = 0; ( i < MAX_LOOPS ) &&
         ( ret == MOSQ_ERR_SUCCESS ) &&
         ( h->connectError == -1 ); i++ )
    {
        ret = mosquitto_loop( h->m, MQTT_SHORT_WAIT_TIME, 1 );
    }

    if( h->connectError > 0 )
    {
        warnx( "%s", mosquitto_connack_string( h->connectError ) );
    }
    else if( ret != MOSQ_ERR_SUCCESS )
    {
        warnx( "connect: %s", mosquitto_strerror( ret ) );
    }

    return h->connectError == 0 ? true : false;
}

/*-----------------------------------------------------------*/

static void closeConnection( handle_t * h )
{
    assert( h != NULL );

    if( h->m != NULL )
    {
        int ret = mosquitto_disconnect( h->m );

        if( ret != MOSQ_ERR_SUCCESS )
        {
            warnx( "closeConnection: %s", mosquitto_strerror( ret ) );
        }
    }
}

/*-----------------------------------------------------------*/

static void on_subscribe( struct mosquitto * m,
                          void * p,
                          int mid,
                          int qos_count,
                          const int * granted_qos )
{
    handle_t * h = p;

    assert( h != NULL );
    assert( granted_qos != NULL );
    assert( qos_count == 1 );

    /* subscribe() is called with a single topic. */
    h->subscribeQOS = granted_qos[ 0 ];
}

/*-----------------------------------------------------------*/

static bool subscribe( handle_t * h,
                       JobsTopic_t api )
{
    int ret;
    char topic[ JOBS_API_MAX_LENGTH( JOBS_THINGNAME_MAX_LENGTH ) ];
    JobsStatus_t jobs_ret;
    size_t i;

    assert( h != NULL );
    assert( MQTT_QOS <= 2 );

    /* populate the topic buffer with the specified API for use
     * in a subscription request */
    jobs_ret = Jobs_GetTopic( topic,
                              sizeof( topic ),
                              h->name,
                              h->nameLength,
                              api,
                              NULL );
    assert( jobs_ret == JobsSuccess );
    ( void ) jobs_ret;

    /* set to default value */
    h->subscribeQOS = -1;

    ret = mosquitto_subscribe( h->m, NULL, topic, MQTT_QOS );

    /* expect the on_subscribe() callback to update h->subscribeQOS */
    for( i = 0; ( i < MAX_LOOPS ) &&
         ( ret == MOSQ_ERR_SUCCESS ) &&
         ( h->subscribeQOS == -1 ); i++ )
    {
        ret = mosquitto_loop( h->m, MQTT_SHORT_WAIT_TIME, 1 );
    }

    if( h->subscribeQOS == 0x80 )
    {
        warnx( "broker rejected subscription" );
    }
    else if( ret != MOSQ_ERR_SUCCESS )
    {
        warnx( "subscribe: %s", mosquitto_strerror( ret ) );
    }

    return ( ( h->subscribeQOS >= 0 ) && ( h->subscribeQOS <= MQTT_QOS ) ) ? true : false;
}

/*-----------------------------------------------------------*/

static bool sendUpdate( handle_t * h,
                        char * jobid,
                        size_t jobidLength,
                        char * report )
{
    bool ret = true;
    JobsStatus_t jobs_ret;
    int m_ret;
    char topic[ JOBS_API_MAX_LENGTH( JOBS_THINGNAME_MAX_LENGTH ) ];

    assert( h != NULL );
    assert( ( jobid != NULL ) && ( jobidLength > 0 ) );
    assert( report != NULL );

    /* populate the topic buffer for an UpdateJobExecution request */
    jobs_ret = Jobs_Update( topic,
                            sizeof( topic ),
                            h->name,
                            h->nameLength,
                            jobid,
                            jobidLength,
                            NULL );
    assert( jobs_ret == JobsSuccess );
    ( void ) jobs_ret;

    m_ret = mosquitto_publish( h->m,
                               NULL,
                               topic,
                               strlen( report ),
                               report,
                               MQTT_QOS,
                               false );

    if( m_ret != MOSQ_ERR_SUCCESS )
    {
        warnx( "sendUpdate: %s", mosquitto_strerror( ret ) );
        ret = false;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static bool parseJob( handle_t * h,
                      const struct mosquitto_message * message )
{
    bool ret = false;
    JSONStatus_t json_ret;
    char * jobid = NULL, * url = NULL;
    size_t jobidLength = 0, urlLength = 0;

    assert( h != NULL );
    assert( message != NULL );
    assert( ( message->payload != NULL ) && ( message->payloadlen > 0 ) );

    json_ret = JSON_Validate( message->payload, message->payloadlen );

    if( json_ret != JSONSuccess )
    {
        warnx( "invalid job document" );
    }
    else
    {
        json_ret = JSON_Search( message->payload,
                                message->payloadlen,
                                "execution.jobId",
                                ( sizeof( "execution.jobId" ) - 1 ),
                                &jobid,
                                &jobidLength );
    }

    if( json_ret == JSONSuccess )
    {
        json_ret = JSON_Search( message->payload,
                                message->payloadlen,
                                "execution.jobDocument.url",
                                ( sizeof( "execution.jobDocument.url" ) - 1 ),
                                &url,
                                &urlLength );
    }

    if( json_ret == JSONSuccess )
    {
        jobid = strndup( jobid, jobidLength );
        url = strndup( url, urlLength );
        assert( ( jobid != NULL ) && ( url != NULL ) );

        h->jobid = jobid;
        h->jobidLength = jobidLength;
        h->url = url;
        h->urlLength = urlLength;
        ret = true;
    }
    else
    {
        if( jobid != NULL )
        {
            jobid[ jobidLength ] = '\0';
            warnx( "missing url; failing job id: %s", jobid );
            ( void ) sendUpdate( h, jobid, jobidLength, makeReport_( "FAILED" ) );
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

void on_message( struct mosquitto * m,
                 void * p,
                 const struct mosquitto_message * message )
{
    handle_t * h = p;
    JobsStatus_t ret;
    JobsTopic_t api;
    char * jobid;
    uint16_t jobidLength;

    assert( h != NULL );
    assert( message->topic != NULL );

    /* identify a Jobs API and a job ID represented in a topic buffer */
    ret = Jobs_MatchTopic( message->topic,
                           strlen( message->topic ),
                           h->name,
                           h->nameLength,
                           &api,
                           &jobid,
                           &jobidLength );
    assert( ret != JobsBadParameter );
    ( void ) ret;

    switch( api )
    {
        /* a job has been added or the current job was canceled */
        case JobsNextJobChanged:
        /* response to a request to describe the next job */
        case JobsDescribeSuccess:

            if( h->runStatus == Running )
            {
                h->forceUpdate = true;
                h->forcePrompt = true;
            }
            else if( h->runStatus == None )
            {
                if( parseJob( h, message ) == true )
                {
                    h->runStatus = Ready;
                }
            }
            else
            {
                warnx( "unexpected message, topic: %s", message->topic );
            }

            break;

        /* The last update was rejected. */
        case JobsUpdateFailed:

            if( ( h->runStatus == Running ) &&
                ( h->jobid != NULL ) &&
                ( h->jobidLength == jobidLength ) &&
                ( strncmp( h->jobid, jobid, jobidLength ) == 0 ) )
            {
                h->runStatus = Cancel;
            }
            else
            {
                warnx( "update failure for unknown job id: %.*s", jobidLength, jobid );
            }

            break;

        /* We seem to receive these even without a subscription. */
        case JobsUpdateSuccess:
            info( "job update success" );
            break;

        case JobsInvalidTopic:
        default:
            warnx( "unknown topic: %s", message->topic );
            break;
    }
}

/*-----------------------------------------------------------*/

static bool sendDescribeNext( handle_t * h )
{
    bool ret = true;
    JobsStatus_t jobs_ret;
    int m_ret;
    char topic[ JOBS_API_MAX_LENGTH( JOBS_THINGNAME_MAX_LENGTH ) ];

    assert( h != NULL );

    /* populate the topic buffer for a DescribeJobExecution request */
    jobs_ret = Jobs_Describe( topic,
                              sizeof( topic ),
                              h->name,
                              h->nameLength,
                              JOBS_API_JOBID_NEXT,
                              JOBS_API_JOBID_NEXT_LENGTH,
                              NULL );
    assert( jobs_ret == JobsSuccess );
    ( void ) jobs_ret;

    m_ret = mosquitto_publish( h->m, NULL, topic, 0, NULL, MQTT_QOS, false );

    if( m_ret != MOSQ_ERR_SUCCESS )
    {
        warnx( "sendDescribeNext: %s", mosquitto_strerror( ret ) );
        ret = false;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static void checkChild( handle_t * h )
{
    pid_t pid;
    int status;

    assert( h != NULL );
    assert( h->child > 0 );

    /* Has the download process exited? */
    pid = waitpid( h->child, &status, WNOHANG );
    assert( pid != -1 );

    switch( pid )
    {
        /* still running */
        case 0:
            h->report = makeReport_( "IN_PROGRESS" );
            break;

        /* exited */
        default:

            /* process exit status 0 means success */
            if( ( pid == h->child ) &&
                ( WIFEXITED( status ) ) &&
                ( WEXITSTATUS( status ) == 0 ) )
            {
                info( "completed job id: %s", h->jobid );
                h->report = makeReport_( "SUCCEEDED" );
            }
            else
            {
                info( "failed job id: %s", h->jobid );
                h->report = makeReport_( "FAILED" );
            }

            h->child = 0;
            h->runStatus = None;
    }
}

/*-----------------------------------------------------------*/

static bool download( handle_t * h )
{
    bool ret = true;
    pid_t pid;

    assert( h != NULL );
    assert( h->jobid != NULL );
    assert( h->url != NULL );

    /* run download as a separate process */
    pid = fork();

#define dir_format    "%s/job-%s.XXXXXX"

    if( pid == 0 )
    {
        /* create a unique download directory */
        char dir_name[ sizeof( DESTINATION_PREFIX ) + h->jobidLength + sizeof( dir_format ) ];

        snprintf( dir_name, sizeof( dir_name ), dir_format, DESTINATION_PREFIX, h->jobid );

        if( mkdtemp( dir_name ) == NULL )
        {
            err( 1, "mkdtemp %s", dir_name );
        }

        if( chdir( dir_name ) == -1 )
        {
            err( 1, "chdir %s", dir_name );
        }

        info( "download directory: %s", dir_name );

        /* exec the download program */
        CURL( h->url );
        /* arrive here only if exec failed */
        err( 1, "execl:" );
    }

    free( h->url );
    h->url = NULL;
    h->child = pid;

    if( pid == -1 )
    {
        warn( "fork" );
        ret = false;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static void cancelDownload( handle_t * h )
{
    assert( h != NULL );

    if( h->child > 0 )
    {
        int ret = kill( h->child, SIGKILL );
        assert( ( ret == 0 ) || ( errno == ESRCH ) );

        if( ret == 0 )
        {
            /* discard the download process exit status */
            ( void ) wait( NULL );
        }
    }

    h->child = 0;
}

/*-----------------------------------------------------------*/

static void on_log( struct mosquitto * m,
                    void * p,
                    int level,
                    const char * log )
{
    assert( log != NULL );

    info( "%s", log );
}

/*-----------------------------------------------------------*/

static void catch( int signal )
{
    errx( 1, "exit on signal: %d", signal );
}

/*-----------------------------------------------------------*/

static bool setup( handle_t * h )
{
    bool ret = false;
    struct sigaction sa = { 0 };

    assert( h != NULL );

    /* ensure teardown() will run for these signals */
    sa.sa_handler = catch;
    sigemptyset( &sa.sa_mask );
    assert( sigaction( SIGHUP, &sa, NULL ) != -1 );
    assert( sigaction( SIGINT, &sa, NULL ) != -1 );
    assert( sigaction( SIGTERM, &sa, NULL ) != -1 );

    mosquitto_lib_init();
    h->m = mosquitto_new( h->name, true, h );

    if( h->m != NULL )
    {
        mosquitto_log_callback_set( h->m, on_log );
        mosquitto_connect_callback_set( h->m, on_connect );
        mosquitto_subscribe_callback_set( h->m, on_subscribe );
        mosquitto_message_callback_set( h->m, on_message );
        ret = true;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static void teardown( int x,
                      void * p )
{
    handle_t * h = p;

    assert( h != NULL );

    if( h->url != NULL )
    {
        free( h->url );
    }

    if( h->jobid != NULL )
    {
        free( h->jobid );
    }

    cancelDownload( h );
    closeConnection( h );
    mosquitto_destroy( h->m );
    mosquitto_lib_cleanup();
}

/*-----------------------------------------------------------*/

int main( int argc,
          char * argv[] )
{
    handle_t h_, * h = &h_;
    time_t now;

    initHandle( h );

    if( parseArgs( h, argc, argv ) == false )
    {
        exit( 1 );
    }

    on_exit( teardown, h );

    if( ( setup( h ) == false ) || ( connect( h ) == false ) )
    {
        errx( 1, "fatal error" );
    }

    if( subscribe( h, JobsNextJobChanged ) == false )
    {
        errx( 1, "fatal error" );
    }

    info( "requesting first job" );

    if( sendDescribeNext( h ) == false )
    {
        errx( 1, "fatal error" );
    }

    h->lastPrompt = time( NULL );

    while( 1 )
    {
        bool ret = true;
        int m_ret;

        m_ret = mosquitto_loop( h->m, MQTT_WAIT_TIME, 1 );

        if( m_ret != MOSQ_ERR_SUCCESS )
        {
            errx( 1, "mosquitto_loop: %s", mosquitto_strerror( m_ret ) );
        }

        now = time( NULL );

        switch( h->runStatus )
        {
            case None:

                if( ( h->forcePrompt == true ) ||
                    ( ( h->pollinv != 0 ) && ( now > ( h->lastPrompt + h->pollinv ) ) ) )
                {
                    h->lastPrompt = now;
                    info( "requesting job" );
                    ret = sendDescribeNext( h );
                    h->forcePrompt = false;
                }

                break;

            case Ready:
                info( "starting job id: %s", h->jobid );
                ret = download( h );

                if( ret == true )
                {
                    h->runStatus = Running;
                    info( "sending first update" );
                    checkChild( h );
                    ret = sendUpdate( h, h->jobid, h->jobidLength, h->report );
                    h->lastUpdate = now;
                }

                break;

            case Running:

                checkChild( h );

                /* send an update if the job exited, was "force" canceled, or a periodic update is due */
                if( ( h->runStatus == None ) ||
                    ( h->forceUpdate == true ) ||
                    ( ( h->updateinv != 0 ) && ( now > ( h->lastUpdate + h->updateinv ) ) ) )
                {
                    info( "updating job id: %s", h->jobid );
                    ret = sendUpdate( h, h->jobid, h->jobidLength, h->report );
                    h->lastUpdate = now;
                    h->forceUpdate = false;
                }

                break;

            case Cancel:
                info( "canceled job id: %s", h->jobid );
                cancelDownload( h );
                h->runStatus = None;
        }

        if( ret == false )
        {
            errx( 1, "fatal error" );
        }

        if( ( h->runStatus == None ) && ( h->jobid != NULL ) )
        {
            free( h->jobid );
            h->jobid = NULL;
            h->jobidLength = 0;

            if( h->runOnce == true )
            {
                break;
            }
        }
    }

    exit( EXIT_SUCCESS );
}
