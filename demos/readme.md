
## Updating MQTT keep alive time

When you increase MQTT keep alive time and observe that the
device is getting disconnected before the MQTT keep alive kicks in,
one possible reason might be that the underlying TCP connection
dies before the MQTT keep alive timer expires. 

One possible solution is to enable TCP keep alive to ensure that the
TCP connection does not die because of inactivity. On BSD (or similar)
sockets it can be enabled by configuring the following options described
in [socket(7)](https://man7.org/linux/man-pages/man7/socket.7.html) and
[tcp(7)](https://man7.org/linux/man-pages/man7/tcp.7.html) man pages:

* `SO_KEEPALIVE` - Keep-alives are sent only when the `SO_KEEPALIVE` socket option is enabled.
* `TCP_KEEPIDLE`- The time (in seconds) the connection needs to remain idle before TCP starts sending keepalive probes, if the socket option `SO_KEEPALIVE` has been set on this socket.
* `TCP_KEEPINTVL` - The time (in seconds) between individual keepalive probes.
* `TCP_KEEPCNT` - The maximum number of keepalive probes TCP should send before dropping the connection.
