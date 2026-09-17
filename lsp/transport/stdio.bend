# transport/stdio: LSP's base protocol over stdin and stdout. Reads bytes (a
# read may end inside a UTF-8 char, and Content-Length counts bytes), keeps
# what is past the current message in buf.
import Base
import ./service.bend as S
import ../frame.bend as Frame

type Stdio is Type:
  Stdio{inp: File, out: File, buf: List<&2, U32>}

# no bytes means the peer closed the pipe
def recv.grown(bytes: List<&2, U32>, inp: File, out: File, buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)) -> IO(Stdio & Maybe<&2, String>):
  match bytes:
    case Nil{}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, []}, None{}))
    case Con{b, t}:
      rest(Stdio{inp, out, List.append(&2, U32, buf, b <> t)})

def recv.fed(r: Result<&1, &1, U32 & String, List<&2, U32>>, inp: File, out: File, buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)) -> IO(Stdio & Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, []}, None{}))
    case Done{bytes}:
      recv.grown(bytes, inp, out, buf, rest)

def recv.read(got: File & Result<&1, &1, U32 & String, List<&2, U32>>, out: File, buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)) -> IO(Stdio & Maybe<&2, String>):
  (inp, r) = got
  recv.fed(r, inp, out, buf, rest)

# a whole message is cut off the buffer; short of one, read and look again
def recv.on(c: Frame.Cut, inp: File, out: File, buf: List<&2, U32>,
  rest: Stdio -> IO(Stdio & Maybe<&2, String>)) -> IO(Stdio & Maybe<&2, String>):
  match c:
    case Frame.Ready{body, left}:
      IO.pure(Stdio & Maybe<&2, String>, (Stdio{inp, out, left}, Some{Frame.decode(body)}))
    case Frame.More{}:
      do IO<Stdio & Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(inp, 65536)
        recv.read(got, out, buf, rest)

def recv.loop(fuel: Nat, h: Stdio) -> IO(Stdio & Maybe<&2, String>):
  match fuel:
    case 0n:
      IO.pure(Stdio & Maybe<&2, String>, (h, None{}))
    case 1n+f:
      Stdio{inp, out, +buf} = h
      recv.on(Frame.cut(buf), inp, out, buf, hh => recv.loop(f, hh))

# the fuel bounds the reads one message may take
def recv(h: Stdio) -> IO(Stdio & Maybe<&2, String>):
  recv.loop(U32.to_nat(1000000), h)

def send.done(w: File & Result<&1, &1, U32 & String, Unit>, inp: File, buf: List<&2, U32>) -> IO(Stdio):
  (out, r) = w
  IO.pure(Stdio, Stdio{inp, out, buf})

def send(h: Stdio, body: String) -> IO(Stdio):
  Stdio{inp, out, buf} = h
  do IO<Stdio>:
    w : File & Result<&1, &1, U32 & String, Unit> <- File.write(out, Frame.wrap(body))
    send.done(w, inp, buf)

# a File for a descriptor the process already holds. Not File.open on
# /dev/stdin: an editor may hand the server sockets, which no path opens
def stdio.fd(n: U32) -> IO(File):
  import "./fd.c"
  import "./fd.js"

def open() -> IO(Stdio):
  do IO<Stdio>:
    inp : File <- stdio.fd(0)
    out : File <- stdio.fd(1)
    return Stdio{inp, out, []}

def new() -> S.Transport<Stdio>:
  S.Transport{recv, send}
