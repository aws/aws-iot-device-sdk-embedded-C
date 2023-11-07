
## Updating MQTT keep alive time

When the MQTT keep alive time is increased and if its observed that the device disconnection is not detected, one possible reason might be that the TCP connection dies because the new MQTT keep alive exceeds the underlying TCP socket's keep alive configuration. On BSD (or similar) sockets it can be enabled by configuring the following options described in [socket(7)](https://man7.org/linux/man-pages/man7/socket.7.html) and [tcp(7)](https://man7.org/linux/man-pages/man7/tcp.7.html) man pages:

* `SO_KEEPALIVE` - Keep-alives are sent only when the `SO_KEEPALIVE` socket option is enabled.
* `TCP_KEEPIDLE`- The time (in seconds) the connection needs to remain idle before TCP starts sending keepalive probes, if the socket option `SO_KEEPALIVE` has been set on this socket.
* `TCP_KEEPINTVL` - The time (in seconds) between individual keepalive probes.
* `TCP_KEEPCNT` - The maximum number of keepalive probes TCP should send before dropping the connection.
