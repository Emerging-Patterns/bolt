# bolt/lsp: the laws. LSP's framing (frame.bend) is pure, so these quantify
# over every message body, every byte that follows it on the wire, and every
# point a read may stop at. The dispatcher's decision (server.bend's step) is
# pure too, so its laws quantify over every stream of messages and whatever
# the work behind each method gave. What a document's diagnostics hold is
# server.bend's pub.* decision, pure over what the IO gave it, so those laws
# quantify over every text, every checker result and every file system.
import Base
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J
import ./frame.bend as Frame
import ./server.bend as Server
import ./docs.bend as Docs
import ./report.bend as Rep
import ./proto.bend as Proto
import ../finding.bend as F
import ../lint/world.bend as W
import ../lint/plan.bend as Plan

# a digit as its char
def digit_char(dd: Frame.Digit) -> Char:
  match dd:
    case Frame.D0{}:
      '0'
    case Frame.D1{}:
      '1'
    case Frame.D2{}:
      '2'
    case Frame.D3{}:
      '3'
    case Frame.D4{}:
      '4'
    case Frame.D5{}:
      '5'
    case Frame.D6{}:
      '6'
    case Frame.D7{}:
      '7'
    case Frame.D8{}:
      '8'
    case Frame.D9{}:
      '9'

# a digit's value
def digit_value(dd: Frame.Digit) -> Nat:
  match dd:
    case Frame.D0{}:
      0n
    case Frame.D1{}:
      1n
    case Frame.D2{}:
      2n
    case Frame.D3{}:
      3n
    case Frame.D4{}:
      4n
    case Frame.D5{}:
      5n
    case Frame.D6{}:
      6n
    case Frame.D7{}:
      7n
    case Frame.D8{}:
      8n
    case Frame.D9{}:
      9n

# ten times n
def tens(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+p:
      Nat.add(10n, tens(p))

# a count's value: its digits, least significant first, in base ten
def value(ds: List<&2, Frame.Digit>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(digit_value(d), tens(value(t)))

# a count as text, most significant digit first
def digits(ds: List<&2, Frame.Digit>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{d, t}:
      digits(t) ++ SCon{digit_char(d), SNil{}}

# the bytes wrap(s) puts on the wire
def wire(ss: String) -> List<&2, U32>:
  Frame.encode(Frame.wrap(ss))

# LAW: Content-Length counts UTF-8 bytes: wrap heads the body with the
# decimal text of a count whose value is the number of bytes the body takes
# in UTF-8
# BOLT-LSP-1
law frame_counts:
  for +s: String
  exs ds: List<&2, Frame.Digit>
  {Frame.wrap(s) == "Content-Length: " ++ digits(ds) ++ "\r\n\r\n" ++ s : String}
    & {value(ds) == List.length(&2, U32, Frame.encode(s)) : Nat}

# LAW: cut of wrap(s) gives s: cut of the wire, whatever follows it, is the
# body's bytes and then the bytes that follow
# BOLT-LSP-1
law frame_round:
  for +s: String
  for more: List<&2, U32>
  {Frame.cut(List.append(&2, U32, wire(s), more)) == Frame.Ready{Frame.encode(s), more} : Frame.Cut}

# LAW: a partial header or body waits: cut of every proper prefix of the wire
# is not yet a message
# BOLT-LSP-1
law frame_waits:
  for +s: String
  for kk: Nat
  for h: {Nat.is_lt(kk, List.length(&2, U32, wire(s))) == True{} : Bool}
  {Frame.cut(List.take(&2, U32, wire(s), kk)) == Frame.More{} : Frame.Cut}

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
def owed(mm: Server.Method, id: J.Json) -> List<&2, J.Json>:
  match mm:
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
def heard(mm: Server.Method, more: List<&2, J.Json>) -> List<&2, J.Json>:
  match mm:
    case Server.MExit{}:
      []
    case other:
      more

def owed_all.go(+mm: Server.Method, id: J.Json, more: List<&2, J.Json>) -> List<&2, J.Json>:
  List.append(&2, J.Json, owed(mm, id), heard(mm, more))

# the ids a stream of messages is owed responses under, in order, up to exit
def owed_all(ts: List<&2, Turn>) -> List<&2, J.Json>:
  match ts:
    case Nil{}:
      []
    case Con{Turn{+msg, w}, rest}:
      owed_all.go(Server.method(Server.name_of(msg)), Server.id_of(msg), owed_all(rest))

# the replies one message leads to
def sent(out: Server.Out) -> List<&2, Server.Reply>:
  Server.Out{rs, quit, docs} = out
  rs

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
# BOLT-LSP-3
law replies_pair:
  for ts: List<&2, Turn>
  {ids(replies(ts)) == owed_all(ts) : List<&2, J.Json>}

# LAW: an unknown request gets -32601 and an unknown notification gets
# nothing: a method the server does not know, whatever its work gave, leads
# to the -32601 error with the message's id, or to no reply without one
# BOLT-LSP-3
law unknown_refused:
  for +name: String
  for h: {Server.method(name) == Server.MOther{} : Server.Method}
  for id: J.Json
  for w: Server.Work
  {sent(Server.step(Server.method(name), id, w)) == refusal(id) : List<&2, Server.Reply>}

# publishing
# ----------

# the notifications a method's work sends
def pub.notes(ww: Server.Work) -> List<&2, String>:
  Server.Work{notes, _answer, _docs} = ww
  notes

# the open documents after a method's work
def pub.docs(ww: Server.Work) -> List<&2, Docs.Doc>:
  Server.Work{_notes, _answer, docs} = ww
  docs

# the CLI's per-file findings in a run, graded the CLI's way: each source's
# per-file rules, each finding at the level the bolt.bend nearest its path
# gives it (BOLT-SCOPE-2 and BOLT-OUT-3 place these among the run's findings)
def pub.cli(+world: W.World) -> List<&2, F.Graded>:
  Plan.grade(Plan.confs(world), world, Plan.per_file(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))))

# LAW: an open document's lint is the CLI's: over every file system and
# working directory (a World), for a document at a path whose text the CLI
# reads as the editor shows it, the LSP's findings on that text, graded by
# the bolt.bend candidates it reads from that same file system and
# directory, are exactly what `bolt <path>` grades as that file's per-file
# findings (none for a bolt.bend, which neither lints)
# BOLT-LSP-2
law lint_is_cli:
  for +world: W.World
  for +path: String
  for +text: String
  for h: {W.paths.of(world) == [path] : List<&2, String>}
  for ht: {W.text(world, path) == Some{text} : Maybe<&2, String>}
  {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)) == pub.cli(world)
    : List<&2, F.Graded>}

# LAW: open publishes the checker's errors plus the lint of the text opened
# BOLT-LSP-4
law open_publishes:
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.open(uri, text, ds, rs, docs))
    == [Server.pub.note(uri, ds, Server.pub.lint(Proto.path(uri), text, rs))] : List<&2, String>}

# LAW: save publishes the checker's new errors plus the lint of the text the
# editor shows
# BOLT-LSP-4
law save_publishes:
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.save(uri, ds, rs, docs))
    == [Server.pub.note(uri, ds, Server.pub.lint(Proto.path(uri), Maybe.default(&2, String, Docs.get(docs, uri), ""),
      rs))] : List<&2, String>}

# LAW: change publishes the lint of the new text plus the checker's errors
# the documents hold for it
# BOLT-LSP-4
law change_publishes:
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.change(uri, text, rs, docs))
    == [Server.pub.note(uri, Docs.errors(docs, uri), Server.pub.lint(Proto.path(uri), text, rs))] : List<&2, String>}

# LAW: after open the documents hold the errors it published and the text
# opened
# BOLT-LSP-4
law open_keeps:
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.open(uri, text, ds, rs, docs)), uri) == ds : List<&2, Rep.Diag>}
    & {Docs.get(pub.docs(Server.pub.open(uri, text, ds, rs, docs)), uri) == Some{text} : Maybe<&2, String>}

# LAW: after save the documents hold the errors it published
# BOLT-LSP-4
law save_keeps:
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.save(uri, ds, rs, docs)), uri) == ds : List<&2, Rep.Diag>}

# LAW: change keeps the checker's errors as they were, so every change
# publishes the last checker result, and keeps the new text
# BOLT-LSP-4
law change_keeps:
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.change(uri, text, rs, docs)), uri) == Docs.errors(docs, uri)
    : List<&2, Rep.Diag>}
    & {Docs.get(pub.docs(Server.pub.change(uri, text, rs, docs)), uri) == Some{text} : Maybe<&2, String>}

# LAW: close publishes an empty list, and forgets the document's errors
# BOLT-LSP-4
law close_publishes:
  for +uri: String
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.close(uri, docs)) == [Server.pub.note(uri, [], [])] : List<&2, String>}
    & {Docs.errors(pub.docs(Server.pub.close(uri, docs)), uri) == [] : List<&2, Rep.Diag>}

# LAW: an open bolt.bend gets no lint, whatever its text and the candidates
# BOLT-LSP-4
law config_unlinted:
  for +path: String
  for h: {Plan.is_config(path) == True{} : Bool}
  for text: String
  for rs: List<&2, Maybe<&2, String>>
  {Server.pub.lint(path, text, rs) == [] : List<&2, F.Graded>}
