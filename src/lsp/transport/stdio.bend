# transport/stdio: LSP's base protocol over stdin and stdout. Reads bytes (a
# read may end inside a UTF-8 char, and Content-Length counts bytes), keeps
# what is past the current message in buf. A read asks for exactly what the
# message in hand lacks (Frame.next): File.read_bytes waits until it has all
# it was asked for (bend 2.0.40), so asking for more than the editor has sent
# is a server that never answers.
#
# Trusted, not proved: the transport effect (fd.c, fd.js) delivers stdin bytes
# in order and writes stdout bytes whole; it is foreign code over descriptors
# 0 and 1.
import Base
import ./service.bend as S
import ../frame.bend as Frame

# the process's stdin and stdout, and the bytes read but not yet framed
type Stdio is Type:  # noqa: L001 transport effect
  Stdio{inp: File, out: File, buf: List<&2, U32>}

# no bytes means the peer closed the pipe
def recv.grown(
  bytes: List<&2, U32>,
  inp: File,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  match bytes:
    case Nil{}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, []}, None{}))
    case Con{b, t}:
      rest(Stdio{inp, out, List.append(&2, U32, buf, b <> t)})

def recv.fed(
  r: Result<&1, &1, U32 & String, List<&2, U32>>,
  inp: File,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, []}, None{}))
    case Done{bytes}:
      recv.grown(bytes, inp, out, buf, rest)

def recv.read(
  got: File & Result<&1, &1, U32 & String, List<&2, U32>>,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  (inp, r) = got
  recv.fed(r, inp, out, buf, rest)

def recv.lined(
  r: Result<&1, &1, U32 & String, String>,
  inp: File,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, []}, None{}))
    case Done{line}:
      recv.grown(Frame.encode(line), inp, out, buf, rest)

def recv.line(
  got: File & Result<&1, &1, U32 & String, String>,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  (inp, r) = got
  recv.lined(r, inp, out, buf, rest)

# what the buffer lacks, read: a header line, or the bytes the body is short
# of, never more than the message in hand
def recv.more(
  n: Frame.Next,
  inp: File,
  out: File,
  buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  match n:
    case Frame.Line{}:
      do IO<Stdio & Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, String> <- File.read_line(inp, 4096)
        recv.line(got, out, buf, rest)
    case Frame.Bytes{count}:
      do IO<Stdio & Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(inp, count)
        recv.read(got, out, buf, rest)

# a whole message is cut off the buffer; short of one, read what it lacks and
# look again
def recv.on(
  c: Frame.Cut,
  inp: File,
  out: File,
  +buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)
) -> IO(Stdio & Maybe<&2, String>):
  match c:
    case Frame.Whole{body, left}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, left}, Some{Frame.decode(body)}))
    case Frame.More{}:
      recv.more(Frame.next(buf), inp, out, buf, rest)

def recv.loop(fuel: Nat, h2: Stdio) -> IO(Stdio & Maybe<&2, String>):
  match fuel:
    case 0n:
      IO.pure(Stdio & Maybe<&2, String>, (h2, None{}))
    case 1n+f:
      Stdio{inp, out, +buf} = h2
      recv.on(Frame.cut(buf), inp, out, buf, h => recv.loop(f, h))

# the fuel bounds the reads one message may take
def recv(h2: Stdio) -> IO(Stdio & Maybe<&2, String>):  # noqa: L001 transport effect
  recv.loop(1000000n, h2)

def send.done(w: File & Result<&1, &1, U32 & String, Unit>, inp: File, buf: List<&2, U32>) -> IO(Stdio):
  (out, r) = w
  IO.pure(Stdio, Stdio{inp, out, buf})

# a body, framed and written
def send(h2: Stdio, body: String) -> IO(Stdio):  # noqa: L001 transport effect
  Stdio{inp, out, buf} = h2
  do IO<Stdio>:
    w : File & Result<&1, &1, U32 & String, Unit> <- File.write(out, Frame.wrap(body))
    send.done(w, inp, buf)

# a File for a descriptor the process already holds. Not File.open on
# /dev/stdin: an editor may hand the server sockets, which no path opens
def stdio.fd(nn: U32) -> IO(File):
  import "./fd.c"
  import "./fd.js"

# the process's descriptors 0 and 1, wrapped
def open() -> IO(Stdio):  # noqa: L001 transport effect
  do IO<Stdio>:
    inp : File <- stdio.fd(0)
    out : File <- stdio.fd(1)
    return Stdio{inp, out, []}

# the transport over stdio
def new() -> S.Transport<Stdio>:  # noqa: L001 effect record
  S.Transport{recv, send}
