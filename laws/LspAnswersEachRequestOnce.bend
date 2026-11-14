# Each request gets exactly one response with the same id, in order; an
# unknown request gets -32601; an unknown notification gets nothing.
import Base
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/server.bend as Server
import ./defs/MessageTurns.bend as D1

# the ids of the responses among replies, in order; a notification has none
def ids(rs: List<&2, Server.Reply>) -> List<&2, J.Json>:
  match rs:
    case Nil{}:
      []
    case Con{Server.RNote{body}, t}:
      ids(t)
    case Con{Server.RResult{id, result}, t}:
      id <> ids(t)
    case Con{Server.RError{id, code, message}, t}:
      id <> ids(t)

# one id for a message that has one, none for a notification
def if_id(id: J.Json) -> List<&2, J.Json>:
  match id:
    case J.JNull{}:
      []
    case other:
      [other]

# the ids a message is owed responses under: its id for a request, its id
# for a method the server does not know when it has one, none for a
# notification or exit
def owed(m: Server.Method, id: J.Json) -> List<&2, J.Json>:
  match m:
    case Server.MInitialize{}:
      [id]
    case Server.MShutdown{}:
      [id]
    case Server.MExit{}:
      []
    case Server.MOpen{}:
      []
    case Server.MChange{}:
      []
    case Server.MSave{}:
      []
    case Server.MClose{}:
      []
    case Server.MHover{}:
      [id]
    case Server.MDefinition{}:
      [id]
    case Server.MSymbols{}:
      [id]
    case Server.MCompletion{}:
      [id]
    case Server.MReferences{}:
      [id]
    case Server.MRename{}:
      [id]
    case Server.MSemantic{}:
      [id]
    case Server.MOther{}:
      if_id(id)

# nothing after exit is heard
def heard(m: Server.Method, more: List<&2, J.Json>) -> List<&2, J.Json>:
  match m:
    case Server.MExit{}:
      []
    case other:
      more

def owed_all.go(+m: Server.Method, id: J.Json, more: List<&2, J.Json>) -> List<&2, J.Json>:
  List.append(&2, J.Json, owed(m, id), heard(m, more))

# the ids a stream of messages is owed responses under, in order, up to exit
def owed_all(ts: List<&2, D1.Turn>) -> List<&2, J.Json>:
  match ts:
    case Nil{}:
      []
    case Con{D1.Turn{+msg, w}, rest}:
      owed_all.go(Server.method(Server.name_of(msg)), Server.id_of(msg), owed_all(rest))

# what a method the server does not know is owed: -32601 with the id, and
# nothing at all for a notification
def refusal(id: J.Json) -> List<&2, Server.Reply>:
  match id:
    case J.JNull{}:
      []
    case other:
      [Server.RError{other, "-32601", "method not found"}]

# LAW: each request gets exactly one response with the same id, in order:
# over every stream of messages, whatever the work behind each method gave,
# the ids of the responses sent are the ids the messages are owed, one per
# request and none for a notification
law replies_pair:
  for ts: List<&2, D1.Turn>
  {ids(D1.replies(ts)) == owed_all(ts) : List<&2, J.Json>}

# LAW: an unknown request gets -32601 and an unknown notification gets
# nothing: a method the server does not know, whatever its work gave, leads
# to the -32601 error with the message's id, or to no reply without one
law unknown_refused:
  for +name: String
  for h: {Server.method(name) == Server.MOther{} : Server.Method}
  for id: J.Json
  for w: Server.Work
  {D1.sent(Server.step(Server.method(name), id, w)) == refusal(id) : List<&2, Server.Reply>}
