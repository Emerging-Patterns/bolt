# bolt/lsp: the laws. LSP's framing (frame.bend) is pure, so these quantify
# over every message body, every byte that follows it on the wire, and every
# point a read may stop at. The dispatcher's decision (server.bend's step) is
# pure too, so its laws quantify over every stream of messages and whatever
# the work behind each method gave.
import Base
import 0xa3c2445eb44c5d8406e6229be518fccb/value.bend as J
import ./frame.bend as Frame
import ./server.bend as Server
import ./report.bend as Rep
import ./checker/argv.bend as Argv
import ./nav.bend as Nav
import ./docs.bend as Docs
import ./files/service.bend as F
import ../../syntax/bind.bend as Bind
import ../../syntax/outline.bend as Outline
import ../../syntax/word.bend as Word

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

# the checker
# -----------

# The checker's runs of bend are data (checker/argv.bend): the real checker
# runs `bend` on each with the run's path and flag and nothing else, and it
# makes a run of the file it is asked about, then at most the one followup
# gives. So every run carries `--check-only`, over every path and every first
# report. That bend checks and never runs `main` under that flag is
# BOLT-TRUST-5.

# LAW: the run that checks a file, whatever its path, is `bend <path>
# --check-only`
# BOLT-LSP-5
law check_only:
  for +path: String
  {Argv.run_of(path) == Argv.Run{path, "--check-only"} : Argv.Run}

# LAW: the run that follows a first report, whatever the report and the
# path, is a `--check-only` run too
# BOLT-LSP-5
law followup_check_only:
  for +ds: List<&2, Rep.Diag>
  for +path: String
  for rr: Argv.Run
  for h: {Argv.followup(ds, path) == Some{rr} : Maybe<&2, Argv.Run>}
  {Argv.flag(rr) == "--check-only" : String}

# navigation
# ----------

# Hover, definition, references and completion read an open document as the
# text the editor shows, and answer from syntax's binder over it
# (BOLT-SYN-5). The laws below hold for every files service and every set of
# open documents, and each answer is run to its end (R and k are whatever
# the loop does next). They prove part of BOLT-LSP-6, which stays pending:
# definition and hover look a dotted use up behind its import alias before
# the file's own items, so `Lib.f()` in a file that has `def Lib.f` and
# `import ./lib.bend as Lib` answers null there, though the binder resolves
# it to the file's item.

# LAW: an open document is read as the text the editor shows, whatever the
# files service holds
# BOLT-LSP-6
law nav_open_text:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for -R: Type
  for k: String -> IO.OP<R>
  {Nav.text_of(~fs, docs, uri, R, k) == k(text) : IO.OP<R>}

# a binder the binder found, in the document
def nav.local(mm: Maybe<&2, Bind.Bind>, uri: String) -> Maybe<&2, Nav.Found>:
  match mm:
    case None{}:
      None{}
    case Some{bb}:
      Some{Nav.Here{uri, bb}}

# the binders the binder found in a text
def nav.binds(bb: Bind.Bound) -> List<&2, Bind.Bind>:
  Bind.Bound{binds, _uses, _scopes} = bb
  binds

# LAW: definition on a binder of the open text is that binder
# BOLT-LSP-6
law nav_definition_binder:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for b: Bind.Bind
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SBind{b}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}

# LAW: definition on a use the binder resolves to a binder of the open text
# lands on that binder
# BOLT-LSP-6
law nav_definition_local:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for n: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}
    : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == k(nav.local(Bind.binder(nav.binds(Bind.bound(text)), tl, tc), uri))
    : IO.OP<R>}

# LAW: hover on a use the binder resolves to a binder of the open text shows
# that binder
# BOLT-LSP-6
law nav_hover_local:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for n: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}
    : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k) == k(nav.local(Bind.binder(nav.binds(Bind.bound(text)), tl, tc), uri))
    : IO.OP<R>}

# the positions of a binder the binder found: an item's or a constructor's
# declaration and uses, any other binder's own position and its uses'
def nav.bind_sites(kind: Bind.BindKind, +name: String, +ll: U32, +cc: U32, +bb: Bind.Bound) -> Nav.Sites:
  match kind:
    case Bind.KItem{}:
      Nav.Sites{True{}, Bind.item_sites(bb, name)}
    case Bind.KCtor{}:
      Nav.Sites{True{}, Bind.item_sites(bb, name)}
    case _other:
      Nav.Sites{True{}, Bind.sites(bb, ll, cc)}

# the positions of a use, by what the binder resolved it to: a binder's, an
# item's, or for a name from Base or behind an alias its uses by that name,
# which are not the document's own
def nav.use_sites(tg: Bind.Target, +name: String, +bb: Bind.Bound) -> Nav.Sites:
  match tg:
    case Bind.TLocal{tl, tc}:
      Nav.Sites{True{}, Bind.sites(bb, tl, tc)}
    case Bind.TItem{item}:
      Nav.Sites{True{}, Bind.item_sites(bb, item)}
    case _other:
      Nav.Sites{False{}, Bind.named_sites(bb, name)}

# the positions references answers for the site the binder found, and
# whether they are the document's own (only those rename)
def nav.referenced(site: Maybe<&2, Bind.Site>, +bb: Bind.Bound) -> Nav.Sites:
  match site:
    case None{}:
      Nav.Sites{False{}, []}
    case Some{Bind.SBind{Bind.Bind{name, l, c, kind, _note}}}:
      nav.bind_sites(kind, name, l, c, bb)
    case Some{Bind.SUse{Bind.Use{name, _l, _c, tg}}}:
      nav.use_sites(tg, name, bb)

# LAW: references answer from the binder over the open text: the positions
# of the binder, item or name the binder finds at the position
# BOLT-LSP-6
law nav_references:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for -R: Type
  for k: Nav.Sites -> IO.OP<R>
  {Nav.sites(~fs, docs, uri, line, col, R, k)
    == k(nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text))) : IO.OP<R>}

# the binders the binder has in scope at a line of a text, those that start
# with the prefix, as completion items
def nav.locals(+text: String, +prefix: String, +line: U32) -> List<&2, Outline.Item>:
  Outline.starting(Nav.as_items(Bind.visible(Bind.bound(text), line)), prefix, "")

# what completion offers after the names the binder has in scope: the
# document's items, its aliases, then what Base gave
def nav.after(+text: String, +prefix: String, base: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  List.append(&2, Outline.Item, Outline.starting(Outline.items(text), prefix, ""),
    List.append(&2, Outline.Item, Outline.aliases(Outline.items(text), prefix), base))

# LAW: completion of a name typed under no import alias of the open text
# offers first the binders the binder has in scope at the line, those that
# start with what is typed, then the document's items, its aliases and Base
# BOLT-LSP-6
law nav_completion:
  for fs: F.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +prefix: String
  for +line: U32
  for hp: {Outline.import_path(Outline.items(text), Word.head(prefix)) == None{} : Maybe<&2, String>}
  for -R: Type
  for k: List<&2, Outline.Item> -> IO.OP<R>
  {Nav.candidates(~fs, docs, uri, prefix, line, R, k)
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, nav.locals(text, prefix, line), nav.after(text, prefix, base))))
    : IO.OP<R>}
