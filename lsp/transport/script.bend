# transport/script: a canned session: the inbox is the messages to receive,
# and every message sent is printed, one body per line.
import Base
import ./service.bend as S

# a canned transport: the messages still to receive
type Script is Type:
  Script{inbox: List<&2, String>}

# the next canned message, or None when they are over
def recv(h: Script) -> IO(Script & Maybe<&2, String>):
  match h:
    case Script{Nil{}}:
      IO.pure(Script & Maybe<&2, String>, (Script{Nil{}}, None{}))
    case Script{Con{m, t}}:
      IO.pure(Script & Maybe<&2, String>, (Script{t}, Some{m}))

# a body printed, as its own line
def send(h: Script, body: String) -> IO(Script):
  do IO<Script>:
    IO.print(body)
    return h

# the canned transport
def new() -> S.Transport<Script>:
  S.Transport{recv, send}
