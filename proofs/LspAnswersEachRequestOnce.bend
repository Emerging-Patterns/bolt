# proofs of laws/LspAnswersEachRequestOnce.bend
import Base
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/server.bend as Server
import ../laws/LspAnswersEachRequestOnce.bend as Laws
import ../laws/defs/MessageTurns.bend as D1

# dispatch
# --------

# notifications carry no response ids
law notices_ids:
  for ns: List<&2, String>
  for -more: List<&2, Server.Reply>
  {Laws.ids(List.append(&2, Server.Reply, Server.notices(ns), more)) == Laws.ids(more) : List<&2, J.Json>}

def notices_ids(ns, more):
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      notices_ids(t, more)

# an unknown method's replies carry its id when it has one
law unknown_ids:
  for id: J.Json
  for -more: List<&2, Server.Reply>
  {Laws.ids(List.append(&2, Server.Reply, Server.unknown(id), more))
    == List.append(&2, J.Json, Laws.if_id(id), Laws.ids(more)) : List<&2, J.Json>}

def unknown_ids(id, _more):
  match id:
    case J.JNull{}:
      {==}
    case J.JBool{b}:
      {==}
    case J.JNum{raw}:
      {==}
    case J.JStr{s}:
      {==}
    case J.JArr{items}:
      {==}
    case J.JObj{pairs}:
      {==}
    case J.JNil{}:
      {==}
    case J.JCons{h, t}:
      {==}
    case J.JPair{k, v, r}:
      {==}
    case J.JSpan{src, n}:
      {==}
    case J.JBind{src, n, v, r}:
      {==}

# a response carries its request's id, a result or an error alike
law respond_ids:
  for -id: J.Json
  for a: Server.Answer
  for -more: List<&2, Server.Reply>
  {Laws.ids(Server.respond(id, a) <> more) == id <> Laws.ids(more) : List<&2, J.Json>}

def respond_ids(_id, a, _more):
  match a:
    case Server.Answer{r}:
      {==}
    case Server.Refusal{c, m}:
      {==}

# one message's replies carry the ids it is owed, then the rest's unless it
# was exit, whatever its work gave
law turn_ids:
  for w: Server.Work
  for m: Server.Method
  for id: J.Json
  for -more: List<&2, Server.Reply>
  {Laws.ids(D1.then(Server.step(m, id, w), more)) == Laws.owed_all.go(m, id, Laws.ids(more))
    : List<&2, J.Json>}

def turn_ids(w, m, id, more):
  match w:
    case Server.Work{notes, answer, docs}:
      match m:
        case Server.MInitialize{}:
          respond_ids(id, answer, more)
        case Server.MShutdown{}:
          respond_ids(id, answer, more)
        case Server.MExit{}:
          {==}
        case Server.MOpen{}:
          notices_ids(notes, more)
        case Server.MChange{}:
          notices_ids(notes, more)
        case Server.MSave{}:
          notices_ids(notes, more)
        case Server.MClose{}:
          notices_ids(notes, more)
        case Server.MHover{}:
          respond_ids(id, answer, more)
        case Server.MDefinition{}:
          respond_ids(id, answer, more)
        case Server.MSymbols{}:
          respond_ids(id, answer, more)
        case Server.MCompletion{}:
          respond_ids(id, answer, more)
        case Server.MReferences{}:
          respond_ids(id, answer, more)
        case Server.MRename{}:
          respond_ids(id, answer, more)
        case Server.MSemantic{}:
          respond_ids(id, answer, more)
        case Server.MOther{}:
          unknown_ids(id, more)

def Laws.replies_pair(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      match t:
        case D1.Turn{+msg, w}:
          +m = Server.method(Server.name_of(msg))
          +id = Server.id_of(msg)
          Equal.trans(List<&2, J.Json>, Laws.ids(D1.then(Server.step(m, id, w), D1.replies(rest))),
            Laws.owed_all.go(m, id, Laws.ids(D1.replies(rest))), Laws.owed_all.go(m, id, Laws.owed_all(rest)),
            turn_ids(w, m, id, D1.replies(rest)),
            Equal.cong(List<&2, J.Json>, List<&2, J.Json>, x => Laws.owed_all.go(m, id, x),
              Laws.ids(D1.replies(rest)), Laws.owed_all(rest), Laws.replies_pair(rest)))

# the method the server does not know is refused with the id, or ignored
# without one, whatever its work gave
law unknown_other:
  for w: Server.Work
  for id: J.Json
  {D1.sent(Server.step(Server.MOther{}, id, w)) == Laws.refusal(id) : List<&2, Server.Reply>}

def unknown_other(w, id):
  match w:
    case Server.Work{notes, answer, docs}:
      match id:
        case J.JNull{}:
          {==}
        case J.JBool{b}:
          {==}
        case J.JNum{raw}:
          {==}
        case J.JStr{s}:
          {==}
        case J.JArr{items}:
          {==}
        case J.JObj{pairs}:
          {==}
        case J.JNil{}:
          {==}
        case J.JCons{h, t}:
          {==}
        case J.JPair{k, v, r}:
          {==}
        case J.JSpan{src, n}:
          {==}
        case J.JBind{src, n, v, r}:
          {==}

def Laws.unknown_refused(name, h, id, w):
  Equal.trans(List<&2, Server.Reply>, D1.sent(Server.step(Server.method(name), id, w)),
    D1.sent(Server.step(Server.MOther{}, id, w)), Laws.refusal(id),
    Equal.cong(Server.Method, List<&2, Server.Reply>, m => D1.sent(Server.step(m, id, w)), Server.method(name),
      Server.MOther{}, h),
    unknown_other(w, id))
