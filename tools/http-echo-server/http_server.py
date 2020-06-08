#!/usr/bin/env python3
"""
HTTP server that responds with information about the request
in JSON format
Usage:
    ./server.py [<port>]
"""

from http.server import BaseHTTPRequestHandler, HTTPServer
import logging
import json


class ServerRequestHandler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def _set_response(self):
        self.send_response(200)
        self.send_header('Content-Type', 'application/json')
        self.end_headers()

    def do_GET(self):
        response_body_dict = {
            'Method': str(self.command),
            'Path': str(self.path),
            'Request Headers': str(self.headers),
        }

        # Get the Content-Length header value from the request and use that
        # to read the request body from the stream
        content_len = int(self.headers.get('Content-Length')
                          ) if self.headers.get('Content-Length') else 0
        if content_len:
            response_body_dict['Request Body'] = self.rfile.read(
                content_len).decode('utf8')

        response_body_str = json.dumps(response_body_dict, indent=4)

        logging.info('Received request:\n{}'.format(response_body_str))

        self._set_response()
        if str(self.command) != "HEAD":
            self.wfile.write(str.encode(response_body_str))

    do_PUT = do_POST = do_HEAD = do_GET


def run(server_class=HTTPServer,
        handler_class=ServerRequestHandler,
        port=8080):
    logging.basicConfig(level=logging.INFO)
    server_address = ('', port)
    httpd = server_class(server_address, handler_class)
    logging.info('Starting http server...')
    try:
        httpd.serve_forever()
    except (KeyboardInterrupt, SystemExit):
        pass
    logging.info('Stopping http server...')
    httpd.server_close()


if __name__ == '__main__':
    from sys import argv

    if len(argv) == 2:
        run(port=int(argv[1]))
    else:
        run()
