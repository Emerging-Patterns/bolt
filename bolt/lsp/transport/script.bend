# transport/script: a canned session: the inbox is the messages to receive,
# and every message sent is printed, one body per line.
import Base
import ./service.bend as S

# a canned transport: the messages still to receive
type Script is Type:  # noqa: L001 transport effect
  Script{inbox: List<&2, String>}

# the next canned message, or None when they are over
def recv(hh: Script) -> IO(Script & Maybe<&2, String>):  # noqa: L001 transport effect
  match hh:
    case Script{Nil{}}:
      IO.pure(Script & Maybe<&2, String>, (Script{Nil{}}, None{}))
    case Script{Con{m, t}}:
      IO.pure(Script & Maybe<&2, String>, (Script{t}, Some{m}))

# a body printed, as its own line
def send(hh: Script, body: String) -> IO(Script):  # noqa: L001 transport effect
  do IO<Script>:
    IO.print(body)
    return hh

# the canned transport
def new() -> S.Transport<Script>:  # noqa: L001 effect record
  S.Transport{recv, send}
