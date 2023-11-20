
## Updating MQTT keep alive time

When you increase MQTT keep alive time and observe that the	device is getting disconnected before the MQTT keep alive kicks in, one possible reason might be that the underlying TCP connection dies before the MQTT keep alive timer expires.

One possible solution is to enable TCP keep alive to ensure that the TCP connection does not die because of inactivity. On BSD (or similar)	sockets it can be enabled by configuring the following options described in [socket(7)](https://man7.org/linux/man-pages/man7/socket.7.html) and [tcp(7)](https://man7.org/linux/man-pages/man7/tcp.7.html) man pages:

* `SO_KEEPALIVE` - Keep-alives are sent only when the `SO_KEEPALIVE` socket option is enabled.
* `TCP_KEEPIDLE`- The time (in seconds) the connection needs to remain idle before TCP starts sending keepalive probes, if the socket option `SO_KEEPALIVE` has been set on this socket.
* `TCP_KEEPINTVL` - The time (in seconds) between individual keepalive probes.
* `TCP_KEEPCNT` - The maximum number of keepalive probes TCP should send before dropping the connection.

Sample code snippet to update TCP keep alive configuration for BSD sockets:

``` c
    int status;
    int keepAliveFlag = 1, keepAliveIdle = 60, keepAliveInterval = 15, keepAliveCount = 4;

    /* Enable keep alive feature. */
    status = setsockopt( *pTcpSocket,
                         SOL_SOCKET,
                         SO_KEEPALIVE,
                         &keepAliveFlag,
                         ( socklen_t ) sizeof( keepAliveFlag ) );
    assert( status == 0 );

    /* If the connection is idle for 60 seconds, send keep
     * alive probe. */
    status = setsockopt( *pTcpSocket,
                         IPPROTO_TCP,
                         TCP_KEEPIDLE,
                         &keepAliveIdle,
                         ( socklen_t ) sizeof( keepAliveIdle ) );
    assert( status == 0 );

    /* When a keep alive probe is unacknowledged, this is time interval
     * between keep alive probes sent. */
    status = setsockopt( *pTcpSocket,
                         IPPROTO_TCP,
                         TCP_KEEPINTVL,
                         &keepAliveInterval,
                         ( socklen_t ) sizeof( keepAliveInterval ) );
    assert( status == 0 );

    /* When these many keep alive probes go unacknowledged, declare the
     * connection dead. */
    status = setsockopt( *pTcpSocket,
                         IPPROTO_TCP,
                         TCP_KEEPCNT,
                         &keepAliveCount,
                         ( socklen_t ) sizeof( keepAliveCount ) );
    assert( status == 0 );

```