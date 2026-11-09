# dispatching messages into replies, one turn at a time
import Base
import ezjson@1.2.0.0/src/value.bend as J
import ../../src/lsp/server.bend as Server

# dispatch
# --------

# a message the server received, and what the work behind its method gave:
# anything the checker, the files and the documents could have made of it
type Turn is Data:
  Turn{msg: J.Json, work: Server.Work}

def then.go(quit: Bool, rs: List<&2, Server.Reply>, more: List<&2, Server.Reply>) -> List<&2, Server.Reply>:
  match quit:
    case True{}:
      rs
    case False{}:
      List.append(&2, Server.Reply, rs, more)

# the replies after one message: its own, then the rest's unless it quit
def then(out: Server.Out, more: List<&2, Server.Reply>) -> List<&2, Server.Reply>:
  Server.Out{rs, quit, docs} = out
  then.go(quit, rs, more)

# one message's replies, then the rest's: the loop hands it to step by its
# method and id
def turned(tt: Turn, more: List<&2, Server.Reply>) -> List<&2, Server.Reply>:
  Turn{+msg, w} = tt
  then(Server.step(Server.method(Server.name_of(msg)), Server.id_of(msg), w), more)

# every reply the dispatcher sends over a stream of messages, in order
def replies(ts: List<&2, Turn>) -> List<&2, Server.Reply>:
  match ts:
    case Nil{}:
      []
    case Con{tt, rest}:
      turned(tt, replies(rest))

# the replies one message leads to
def sent(out: Server.Out) -> List<&2, Server.Reply>:
  Server.Out{rs, quit, docs} = out
  rs
