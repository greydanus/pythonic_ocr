# flipflop - a FastCGI/WSGI gateway
#
# Copyright © 2005, 2006 Allan Saddi <allan@saddi.com>
# Copyright © 2013 Kozea <contact@kozea.fr>
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
# OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
# HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.

"""
flipflop - a FastCGI/WSGI gateway.

For more information about FastCGI, see <http://www.fastcgi.com/>.

For more information about the Web Server Gateway Interface, see
<http://www.python.org/peps/pep-3333.html>.

Example usage::

  #!/usr/bin/env python
  from myapplication import app  # Assume app is your WSGI application object
  from flipflop import WSGIServer
  WSGIServer(app).run()

"""

import os
import sys
import socket
import select
import signal
import struct
import errno
import threading
import fcntl
import resource
import traceback

# Constants from the spec.
FCGI_LISTENSOCK_FILENO = 0

FCGI_HEADER_LEN = 8

FCGI_VERSION_1 = 1

FCGI_BEGIN_REQUEST = 1
FCGI_ABORT_REQUEST = 2
FCGI_END_REQUEST = 3
FCGI_PARAMS = 4
FCGI_STDIN = 5
FCGI_STDOUT = 6
FCGI_STDERR = 7
FCGI_DATA = 8
FCGI_GET_VALUES = 9
FCGI_GET_VALUES_RESULT = 10
FCGI_UNKNOWN_TYPE = 11
FCGI_MAXTYPE = FCGI_UNKNOWN_TYPE

FCGI_NULL_REQUEST_ID = 0

FCGI_KEEP_CONN = 1

FCGI_RESPONDER = 1
FCGI_AUTHORIZER = 2
FCGI_FILTER = 3

FCGI_REQUEST_COMPLETE = 0
FCGI_CANT_MPX_CONN = 1
FCGI_OVERLOADED = 2
FCGI_UNKNOWN_ROLE = 3

FCGI_MAX_CONNS = 'FCGI_MAX_CONNS'
FCGI_MAX_REQS = 'FCGI_MAX_REQS'
FCGI_MPXS_CONNS = 'FCGI_MPXS_CONNS'

FCGI_Header = '!BBHHBx'
FCGI_BeginRequestBody = '!HB5x'
FCGI_EndRequestBody = '!LB3x'
FCGI_UnknownTypeBody = '!B7x'

FCGI_EndRequestBody_LEN = struct.calcsize(FCGI_EndRequestBody)
FCGI_UnknownTypeBody_LEN = struct.calcsize(FCGI_UnknownTypeBody)


class InputStream(object):
    """File-like object for STDIN and DATA FastCGI input streams."""
    # Limit the size of the InputStream's string buffer to this size + the
    # server's maximum Record size. Since the InputStream is not seekable,
    # we throw away already-read data once this certain amount has been read.
    threshold = 102400 - 8192

    def __init__(self, conn):
        self._conn = conn
        self._buffer = b''
        self._buffers = []
        self._pos = 0  # Current read position.
        self._avail = 0  # Number of bytes currently available.
        self._eof = False  # True when server has sent EOF notification.

    def _shrink_buffer(self):
        """Get rid of already read data (since we can't rewind)."""
        if self._pos >= self.threshold:
            self._buffer = self._buffer[self._pos:]
            self._avail -= self._pos
            self._pos = 0
            assert self._avail >= 0

    def read(self, n=-1):
        if self._pos == self._avail and self._eof:
            return b''
        while True:
            if n < 0 or (self._avail - self._pos) < n:
                # Not enough data available.
                if self._eof:
                    # And there's no more coming.
                    new_position = self._avail
                    break
                else:
                    # Wait for more data.
                    self._conn.process_input()
                    continue
            else:
                new_position = self._pos + n
                break
        # Merge buffer list, if necessary.
        if self._buffers:
            self._buffer += b''.join(self._buffers)
            self._buffers = []
        part = self._buffer[self._pos:new_position]
        self._pos = new_position
        self._shrink_buffer()
        return part

    def readline(self, length=None):
        if self._pos == self._avail and self._eof:
            return b''
        while True:
            # Unfortunately, we need to merge the buffer list early.
            if self._buffers:
                self._buffer += b''.join(self._buffers)
                self._buffers = []
            # Find newline.
            i = self._buffer.find(b'\n', self._pos)
            if i < 0:
                # Not found?
                if self._eof:
                    # No more data coming.
                    new_position = self._avail
                    break
                else:
                    if (length is not None and
                            len(self._buffer) >= length + self._pos):
                        new_position = self._pos + length
                        break
                    # Wait for more to come.
                    self._conn.process_input()
                    continue
            else:
                new_position = i + 1
                break
        part = self._buffer[self._pos:new_position]
        self._pos = new_position
        self._shrink_buffer()
        return part

    def readlines(self, sizehint=0):
        total = 0
        lines = []
        line = self.readline()
        while line:
            lines.append(line)
            total += len(line)
            if 0 < sizehint <= total:
                break
            line = self.readline()
        return lines

    def __iter__(self):
        return self

    def __next__(self):
        line = self.readline()
        if not line:
            raise StopIteration
        return line

    def add_data(self, data):
        if not data:
            self._eof = True
        else:
            self._buffers.append(data)
            self._avail += len(data)


class OutputStream(object):
    """File-like object for STDOUT and STDERR FastCGI output streams.

    If buffered is set to False, calls to write() or writelines() immediately
    result in Records being sent back to the server.

    """
    def __init__(self, conn, req, type, buffered=False):
        self._conn = conn
        self._req = req
        self._type = type
        self._buffered = buffered
        self._buffers = []  # Used if buffered is True
        self.data_written = False
        self.closed = False

    def _write(self, data):
        length = len(data)
        while length:
            to_write = min(length, self._req.server.maxwrite - FCGI_HEADER_LEN)

            rec = Record(self._type, self._req.request_id)
            rec.content_length = to_write
            rec.content_data = data[:to_write]
            self._conn.write_record(rec)

            data = data[to_write:]
            length -= to_write

    def write(self, data):
        assert not self.closed

        if not data:
            return
        if type(data) == str:
            data = data.encode()

        self.data_written = True

        if self._buffered:
            self._buffers.append(data)
        else:
            self._write(data)

    def writelines(self, lines):
        assert not self.closed

        for line in lines:
            self.write(line)

    def flush(self):
        # Only need to flush if this OutputStream is actually buffered.
        if self._buffered:
            data = b''.join(self._buffers)
            self._buffers = []
            self._write(data)

    # Though available, the following should NOT be called by WSGI apps.
    def close(self):
        """Send end-of-stream notification, if necessary."""
        if not self.closed and self.data_written:
            self.flush()
            rec = Record(self._type, self._req.request_id)
            self._conn.write_record(rec)
            self.closed = True


def decode_pair(string, position=0):
    """Decode a name/value pair.

    The number of bytes decoded as well as the name/value pair
    are returned.

    """
    name_length = string[position]
    if name_length & 128:
        name_length = struct.unpack(
            '!L', string[position:position+4])[0] & 0x7fffffff
        position += 4
    else:
        position += 1

    value_length = string[position]
    if value_length & 128:
        value_length = struct.unpack(
            '!L', string[position:position+4])[0] & 0x7fffffff
        position += 4
    else:
        position += 1

    name = string[position:position+name_length]
    position += name_length
    value = string[position:position+value_length]
    position += value_length

    return (position, (name, value))


def encode_pair(name, value):
    """Encode a name/value pair.

    The encoded string is returned.

    """
    name_length = len(name)
    if name_length < 128:
        string = bytes([name_length])
    else:
        string = struct.pack('!L', name_length | 0x80000000)

    value_length = len(value)
    if value_length < 128:
        string += bytes([value_length])
    else:
        string += struct.pack('!L', value_length | 0x80000000)

    return string + name + value


class Record(object):
    """FastCGI Record.

    Used for encoding/decoding records.

    """
    def __init__(self, fcgi_type=FCGI_UNKNOWN_TYPE,
                 request_id=FCGI_NULL_REQUEST_ID):
        self.version = FCGI_VERSION_1
        self.fcgi_type = fcgi_type
        self.request_id = request_id
        self.content_length = 0
        self.padding_length = 0
        self.content_data = b''

    @staticmethod
    def _recvall(sock, length):
        """Attempt to receive length bytes from a socket.

        Socket may be blocking or non-blocking.

        """
        data_list = []
        recv_len = 0
        while length:
            try:
                data = sock.recv(length)
            except socket.error as exception:
                if exception.args[0] == errno.EAGAIN:
                    select.select([sock], [], [])
                    continue
                else:
                    raise
            if not data:  # EOF
                break
            data_list.append(data)
            data_len = len(data)
            recv_len += data_len
            length -= data_len
        return b''.join(data_list), recv_len

    def read(self, sock):
        """Read and decode a Record from a socket."""
        try:
            header, length = self._recvall(sock, FCGI_HEADER_LEN)
        except:
            raise EOFError

        if length < FCGI_HEADER_LEN:
            raise EOFError

        self.version, self.fcgi_type, self.request_id, self.content_length, \
            self.padding_length = struct.unpack(FCGI_Header, header)

        if self.content_length:
            try:
                self.content_data, length = self._recvall(
                    sock, self.content_length)
            except:
                raise EOFError

            if length < self.content_length:
                raise EOFError

        if self.padding_length:
            try:
                self._recvall(sock, self.padding_length)
            except:
                raise EOFError

    @staticmethod
    def _sendall(sock, data):
        """Write data to a socket, don't return until all the data is sent."""
        length = len(data)
        while length:
            try:
                sent = sock.send(data)
            except socket.error as exception:
                if exception.args[0] == errno.EAGAIN:
                    select.select([], [sock], [])
                    continue
                else:
                    raise
            data = data[sent:]
            length -= sent

    def write(self, sock):
        """Encode and write a Record to a socket."""
        self.padding_length = -self.content_length & 7

        header = struct.pack(
            FCGI_Header, self.version, self.fcgi_type, self.request_id,
            self.content_length, self.padding_length)
        self._sendall(sock, header)
        if self.content_length:
            self._sendall(sock, self.content_data)
        if self.padding_length:
            self._sendall(sock, b'\x00' * self.padding_length)


class Request(object):
    """Single FastCGI request.

    These objects are passed to your handler and is the main interface
    between your handler and the fcgi module. The methods should not
    be called by your handler. However, server, params, stdin, stdout,
    stderr, and data are free for your handler's use.

    """
    def __init__(self, conn):
        self._conn = conn

        self.server = conn.server
        self.params = {}
        self.stdin = InputStream(conn)
        self.stdout = OutputStream(conn, self, FCGI_STDOUT)
        self.stderr = OutputStream(conn, self, FCGI_STDERR, buffered=True)
        self.data = InputStream(conn)

    def run(self):
        """Run the handler, flush the streams and end the request."""
        try:
            protocol_status, app_status = self.server.handler(self)
        except:
            traceback.print_exc(file=self.stderr)
            self.stderr.flush()
            if not self.stdout.data_written:
                self.stdout.write(
                    b'Status: 500 Internal Server Error\r\n'
                    b'Content-Type: text/html\r\n\r\n'
                    b'<!doctype html>\r\n'
                    b'<title>Unhandled Exception</title>\r\n'
                    b'<h1>Unhandled Exception</h1>\r\n'
                    b'Unhandled exception thrown by the application.\r\n')
            protocol_status, app_status = FCGI_REQUEST_COMPLETE, 0

        try:
            self.stdout.close()
            self.stderr.close()
            self._conn.end_request(self, app_status, protocol_status)
        except socket.error as exception:
            if exception.args[0] != errno.EPIPE:
                raise


class Connection(object):
    """Connection with the web server.

    Each Connection is associated with a single socket (which is
    connected to the web server) and is responsible for handling all
    the FastCGI message processing for that socket.

    """
    def __init__(self, sock, addr, server):
        self._sock = sock
        self._addr = addr
        self.server = server

        # Active Requests for this Connection, mapped by request ID.
        self._requests = {}

    def _cleanup_socket(self):
        """Close the Connection's socket."""
        try:
            self._sock.shutdown(socket.SHUT_WR)
        except:
            return
        try:
            while True:
                rlist = select.select([self._sock], [], [])[0]
                if not rlist or not self._sock.recv(1024):
                    break
        except:
            pass
        self._sock.close()

    def run(self):
        """Begin processing data from the socket."""
        self._keep_going = True
        while self._keep_going:
            try:
                self.process_input()
            except (EOFError, KeyboardInterrupt):
                break
            except (select.error, socket.error) as exception:
                if exception.args[0] == errno.EBADF:
                    # Socket was closed by Request.
                    break
                raise

        self._cleanup_socket()

    def process_input(self):
        """Attempt to read a single Record from the socket and process it."""
        # Currently, any children Request threads notify this Connection
        # that it is no longer needed by closing the Connection's socket.
        # We need to put a timeout on select, otherwise we might get
        # stuck in it indefinitely... (I don't like this solution.)
        while self._keep_going:
            try:
                rlist = select.select([self._sock], [], [], 1.0)[0]
            except ValueError:
                # Sigh. ValueError gets thrown sometimes when passing select
                # a closed socket.
                raise EOFError
            if rlist:
                break
        if not self._keep_going:
            return
        inrec = Record()
        inrec.read(self._sock)

        if inrec.fcgi_type == FCGI_GET_VALUES:
            outrec = Record(FCGI_GET_VALUES_RESULT)

            position = 0
            while position < inrec.content_length:
                position, (name, _) = decode_pair(inrec.content_data, position)
                cap = self.server.capability.get(name)
                if cap is not None:
                    outrec.content_data += encode_pair(
                        name, str(cap).encode('latin-1'))

            outrec.content_length = len(outrec.content_data)
            self.write_record(outrec)
        elif inrec.fcgi_type == FCGI_BEGIN_REQUEST:
            role, flags = struct.unpack(
                FCGI_BeginRequestBody, inrec.content_data)
            req = Request(self)
            req.request_id, req.role, req.flags = inrec.request_id, role, flags
            req.aborted = False
            if self._requests:
                self.end_request(req, 0, FCGI_CANT_MPX_CONN, remove=False)
            else:
                self._requests[inrec.request_id] = req
        elif inrec.fcgi_type == FCGI_ABORT_REQUEST:
            req = self._requests.get(inrec.request_id)
            if req is not None:
                req.aborted = True
        elif inrec.fcgi_type == FCGI_PARAMS:
            req = self._requests.get(inrec.request_id)
            if req is not None:
                if inrec.content_length:
                    position = 0
                    while position < inrec.content_length:
                        position, (name, value) = decode_pair(
                            inrec.content_data, position)
                        req.params[name.decode('latin-1')] = \
                            value.decode('latin-1')
                else:
                    req.run()
        elif inrec.fcgi_type == FCGI_STDIN:
            req = self._requests.get(inrec.request_id)
            if req is not None:
                req.stdin.add_data(inrec.content_data)
        elif inrec.fcgi_type == FCGI_DATA:
            req = self._requests.get(inrec.request_id)
            if req is not None:
                req.data.add_data(inrec.content_data)
        elif inrec.request_id == FCGI_NULL_REQUEST_ID:
            outrec = Record(FCGI_UNKNOWN_TYPE)
            outrec.content_data = struct.pack(
                FCGI_UnknownTypeBody, inrec.fcgi_type)
            outrec.content_length = FCGI_UnknownTypeBody_LEN
            self.write_record(outrec)
        else:
            # TODO: Need to complain about this.
            pass

    def write_record(self, rec):
        """
        Write a Record to the socket.
        """
        rec.write(self._sock)

    def end_request(self, req, app_status=0,
                    protocol_status=FCGI_REQUEST_COMPLETE, remove=True):
        """
        End a Request.

        Called by Request objects. An FCGI_END_REQUEST Record is
        sent to the web server. If the web server no longer requires
        the connection, the socket is closed, thereby ending this
        Connection (run() returns).
        """
        rec = Record(FCGI_END_REQUEST, req.request_id)
        rec.content_data = struct.pack(
            FCGI_EndRequestBody, app_status, protocol_status)
        rec.content_length = FCGI_EndRequestBody_LEN
        self.write_record(rec)

        if remove:
            del self._requests[req.request_id]

        if not (req.flags & FCGI_KEEP_CONN) and not self._requests:
            self._cleanup_socket()
            self._keep_going = False


class ThreadPool(object):
    """Thread pool.

    Thread pool that maintains the number of idle threads between
    min_spare and max_spare inclusive. By default, there is no limit on
    the number of threads that can be started, but this can be controlled
    by max_threads.

    """
    def __init__(self, min_spare=1, max_spare=5, max_threads=sys.maxsize):
        self._min_spare = min_spare
        self._max_spare = max_spare
        self._max_threads = max(min_spare, max_threads)

        self._lock = threading.Condition()
        self._work_queue = []
        self._idle_count = self._worker_count = max_spare

        self._threads = []
        self._stop = False

        # Start the minimum number of worker threads.
        for _ in range(max_spare):
            self._start_new_thread()

    def _start_new_thread(self):
        thread = threading.Thread(target=self._worker)
        self._threads.append(thread)
        thread.setDaemon(True)
        thread.start()
        return thread

    def shutdown(self):
        """Shutdown all workers."""
        self._lock.acquire()
        self._stop = True
        self._lock.notifyAll()
        self._lock.release()

        # wait for all threads to finish
        for thread in self._threads[:]:
            thread.join()

    def add_job(self, job):
        """Adds a job to the work queue.

        The job object should have a run() method. Return True if the job was
        queued, False otherwise.

        """
        self._lock.acquire()
        try:
            # Maintain minimum number of spares.
            while (self._idle_count < self._min_spare and
                   self._worker_count < self._max_threads):
                try:
                    self._start_new_thread()
                except:
                    return False
                self._worker_count += 1
                self._idle_count += 1

            # Hand off the job.
            if self._idle_count:
                self._work_queue.append(job)
                self._lock.notify()
                return True
            else:
                return False
        finally:
            self._lock.release()

    def _worker(self):
        """Worker thread routine: wait for a job, execute it, repeat."""
        self._lock.acquire()
        try:
            while True:
                while not self._work_queue and not self._stop:
                    self._lock.wait()

                if self._stop:
                    return

                # We have a job to do...
                job = self._work_queue.pop(0)

                assert self._idle_count > 0
                self._idle_count -= 1

                self._lock.release()

                try:
                    job.run()
                except:
                    # FIXME: This should really be reported somewhere.
                    # But we can't simply report it to stderr because of fcgi
                    pass

                self._lock.acquire()

                if self._idle_count == self._max_spare:
                    break  # NB: lock still held
                self._idle_count += 1
                assert self._idle_count <= self._max_spare

            # Die off...
            assert self._worker_count > self._max_spare
            self._threads.remove(threading.currentThread())
            self._worker_count -= 1
        finally:
            self._lock.release()


class WSGIServer(object):
    """FastCGI server that supports the Web Server Gateway Interface."""
    # The maximum number of bytes (per Record) to write to the server.
    # I've noticed mod_fastcgi has a relatively small receive buffer (8K or
    # so).
    maxwrite = 8192

    def __init__(self, application):
        self.application = application
        self.environ = {}
        max_connections = resource.getrlimit(resource.RLIMIT_NOFILE)[0]
        self.capability = {
            FCGI_MAX_CONNS: max_connections,
            FCGI_MAX_REQS: max_connections,
            FCGI_MPXS_CONNS: 0}
        self._thread_pool = ThreadPool()

    def shutdown(self):
        """Wait for running threads to finish."""
        self._thread_pool.shutdown()

    # Signal handlers

    def _hup_handler(self, signum, frame):
        self._hup_received = True
        self._keep_going = False

    def _int_handler(self, signum, frame):
        self._keep_going = False

    def handler(self, req):
        """Special handler for WSGI."""
        if req.role != FCGI_RESPONDER:
            return FCGI_UNKNOWN_ROLE, 0

        # Mostly taken from example CGI gateway.
        environ = req.params
        environ.update(self.environ)

        environ['wsgi.version'] = (1, 0)
        environ['wsgi.input'] = req.stdin
        environ['wsgi.errors'] = req.stderr
        environ['wsgi.multithread'] = True
        environ['wsgi.multiprocess'] = False
        environ['wsgi.run_once'] = False

        if environ.get('HTTPS', 'off') in ('on', '1'):
            environ['wsgi.url_scheme'] = 'https'
        else:
            environ['wsgi.url_scheme'] = 'http'

        self._sanitize_env(environ)

        headers_set = []
        headers_sent = []
        result = None

        def write(data):
            if type(data) is str:
                data = data.encode('latin-1')

            assert type(data) is bytes, 'write() argument must be bytes'
            assert headers_set, 'write() before start_response()'

            if not headers_sent:
                status, response_headers = headers_sent[:] = headers_set
                found = False
                for header, value in response_headers:
                    if header.lower() == b'content-length':
                        found = True
                        break
                if not found and result is not None:
                    try:
                        if len(result) == 1:
                            response_headers.append((
                                b'Content-Length',
                                str(len(data)).encode('latin-1')))
                    except:
                        pass
                string = b'Status: ' + status + b'\r\n'
                for header, value in response_headers:
                    string += header + b': ' + value + b'\r\n'
                string += b'\r\n'
                req.stdout.write(string)

            req.stdout.write(data)
            req.stdout.flush()

        def start_response(status, response_headers, exc_info=None):
            if exc_info:
                try:
                    if headers_sent:
                        # Re-raise if too late
                        info = exc_info[0](exc_info[1])
                        raise info.with_traceback(exc_info[2])
                finally:
                    exc_info = None  # avoid dangling circular ref
            else:
                assert not headers_set, 'Headers already set!'

            if isinstance(status, str):
                status = status.encode('latin-1')

            assert type(status) is bytes, 'Status must be a string'
            assert len(status) >= 4, 'Status must be at least 4 characters'
            assert int(status[:3]), 'Status must begin with 3-digit code'
            assert status[3] == 0x20, 'Status must have a space after code'
            assert type(response_headers) is list, 'Headers must be a list'
            new_response_headers = []
            for name, value in response_headers:
                if isinstance(name, str):
                    name = name.encode('latin-1')
                if isinstance(value, str):
                    value = value.encode('latin-1')

                assert isinstance(name, bytes), (
                    'Header name "%s" must be bytes' % name)
                assert isinstance(value, bytes), (
                    'Value of header "%s" must be bytes' % name)

                new_response_headers.append((name, value))

            headers_set[:] = [status, new_response_headers]
            return write

        try:
            result = self.application(environ, start_response)
            try:
                for data in result:
                    if data:
                        write(data)
                if not headers_sent:
                    write(b'')  # in case body was empty
            finally:
                if hasattr(result, 'close'):
                    result.close()
        except socket.error as exception:
            if exception.args[0] != errno.EPIPE:
                raise  # Don't let EPIPE propagate beyond server

        return FCGI_REQUEST_COMPLETE, 0

    def _sanitize_env(self, environ):
        """Ensure certain values are present, if required by WSGI."""
        if 'SCRIPT_NAME' not in environ:
            environ['SCRIPT_NAME'] = ''

        req_uri = None
        if 'REQUEST_URI' in environ:
            req_uri = environ['REQUEST_URI'].split('?', 1)

        if 'PATH_INFO' not in environ or not environ['PATH_INFO']:
            if req_uri is not None:
                script_name = environ['SCRIPT_NAME']
                if not req_uri[0].startswith(script_name):
                    environ['wsgi.errors'].write(
                        'WARNING: SCRIPT_NAME does not match REQUEST_URI')
                environ['PATH_INFO'] = req_uri[0][len(script_name):]
            else:
                environ['PATH_INFO'] = ''
        if 'QUERY_STRING' not in environ or not environ['QUERY_STRING']:
            if req_uri is not None and len(req_uri) > 1:
                environ['QUERY_STRING'] = req_uri[1]
            else:
                environ['QUERY_STRING'] = ''

        # If any of these are missing, it probably signifies a broken
        # server...
        for name, default in [('REQUEST_METHOD', 'GET'),
                              ('SERVER_NAME', 'localhost'),
                              ('SERVER_PORT', '80'),
                              ('SERVER_PROTOCOL', 'HTTP/1.0')]:
            if name not in environ:
                environ['wsgi.errors'].write(
                    '%s: missing FastCGI param %s required by WSGI!\n' %
                    (self.__class__.__name__, name))
                environ[name] = default

    def run(self):
        """Main loop.

        Exit on SIGHUP, SIGINT, SIGTERM. Return True if SIGHUP was received,
        False otherwise.

        """
        self._web_server_addrs = os.environ.get('FCGI_WEB_SERVER_ADDRS')
        if self._web_server_addrs is not None:
            self._web_server_addrs = [
                x.strip() for x in self._web_server_addrs.split(',')]

        sock = socket.fromfd(
            FCGI_LISTENSOCK_FILENO, socket.AF_INET, socket.SOCK_STREAM)
        try:
            sock.getpeername()
        except socket.error as exception:
            if exception.args[0] != errno.ENOTCONN:
                raise

        # Set up signal handlers.
        self._keep_going = True
        self._hup_received = False

        supported_signals = [signal.SIGINT, signal.SIGTERM]
        if hasattr(signal, 'SIGHUP'):
            supported_signals.append(signal.SIGHUP)

        old_sigs = [(x, signal.getsignal(x)) for x in supported_signals]

        for sig in supported_signals:
            if hasattr(signal, 'SIGHUP') and sig == signal.SIGHUP:
                signal.signal(sig, self._hup_handler)
            else:
                signal.signal(sig, self._int_handler)

        # Set close-on-exec
        fcntl.fcntl(sock.fileno(), fcntl.F_SETFD, fcntl.FD_CLOEXEC)

        # Main loop.
        while self._keep_going:
            try:
                rlist = select.select([sock], [], [], 1.0)[0]
            except select.error as exception:
                if exception.args[0] == errno.EINTR:
                    continue
                raise

            if rlist:
                try:
                    client_socket, addr = sock.accept()
                except socket.error as exception:
                    if exception.args[0] in (errno.EINTR, errno.EAGAIN):
                        continue
                    raise

                fcntl.fcntl(
                    client_socket.fileno(), fcntl.F_SETFD, fcntl.FD_CLOEXEC)

                if not (self._web_server_addrs is None or
                        (len(addr) == 2 and
                         addr[0] in self._web_server_addrs)):
                    client_socket.close()
                    continue

                # Hand off to Connection.
                conn = Connection(client_socket, addr, self)
                if not self._thread_pool.add_job(conn):
                    # No thread left, immediately close the socket to hopefully
                    # indicate to the web server that we're at our limit...
                    # and to prevent having too many opened (and useless)
                    # files.
                    client_socket.close()

        for signum, handler in old_sigs:
            signal.signal(signum, handler)

        # Return bool based on whether or not SIGHUP was received.
        sock.close()
        self.shutdown()

        return self._hup_received
