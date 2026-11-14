# lsp/server: the loop. The transport the messages ride on, the files
# behind imports and Base, and the checker behind the diagnostics are passed
# in (transport/, files/, checker/answer.bend's Checker; checker/bend.bend's
# service is the real checker). The open documents are the
# loop's state. The checker runs on open and save, against the file on disk;
# the linter on every open, change and save, on the text the editor shows,
# each file told the role the imports of the tree give it, read as `bolt
# <path>` reads them (src/lint/plan.bend's graph) on open and save and kept
# for the changes between.
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ./proto.bend as Proto
import ./docs.bend as Docs
import ./nav.bend as Nav
import ./semantic.bend as Semantic
import ../rules.bend as Lint
import ../finding.bend as Finding
import ../config.bend as Config
import ../lint/plan.bend as Plan
import ../lint/world.bend as W
import ../role.bend as Role
import ../src.bend as Src
import ../noqa.bend as Noqa
import ./transport/service.bend as T
import ./checker/answer.bend as C
import ./files/service.bend as F
import ./report.bend as Rep
import ./enc.bend as Enc
import ../syntax/outline.bend as Outline
import ../syntax/lex.bend as Lex
import ../syntax/word.bend as Word

# the methods the server answers; MOther is anything else
type Method is Data:
  MInitialize{}
  MShutdown{}
  MExit{}
  MOpen{}
  MChange{}
  MSave{}
  MClose{}
  MHover{}
  MDefinition{}
  MSymbols{}
  MCompletion{}
  MReferences{}
  MRename{}
  MSemantic{}
  MOther{}

# a message the server sends: a notification, already printed, or the
# response to a request, its result or its error
type Reply is Data:
  RNote{body: String}
  RResult{id: J.Json, result: J.Json}
  RError{id: J.Json, code: String, message: String}

# what a request is answered with: a result, or an error's code and message
type Answer is Data:
  Answer{result: J.Json}
  Refusal{code: String, message: String}

# what the work behind a method gave: the notifications it sends, the answer
# (read for a request only), the documents after it. It never sees the id
type Work is Data:
  Work{notes: List<&2, String>, answer: Answer, docs: List<&2, Docs.Doc>}

# what one message leads to: the replies to send, whether to stop, the documents
type Out is Data:
  Out{replies: List<&2, Reply>, quit: Bool, docs: List<&2, Docs.Doc>}

# how the server treats a method: a request owed one response, a
# notification, exit, or a method it does not know
type Role is Data:
  RRequest{}
  RNotice{}
  RExit{}
  RUnknown{}

# a method by its name
def method(+name: String) -> Method:
  Bool.pick(Method, String.eq(name, "initialize"), MInitialize{},
    Bool.pick(Method, String.eq(name, "shutdown"), MShutdown{},
      Bool.pick(Method, String.eq(name, "exit"), MExit{},
        Bool.pick(Method, String.eq(name, "textDocument/didOpen"), MOpen{},
          Bool.pick(Method, String.eq(name, "textDocument/didChange"), MChange{},
            Bool.pick(Method, String.eq(name, "textDocument/didSave"), MSave{},
              Bool.pick(Method, String.eq(name, "textDocument/didClose"), MClose{},
                Bool.pick(Method, String.eq(name, "textDocument/hover"), MHover{},
                  Bool.pick(Method, String.eq(name, "textDocument/definition"), MDefinition{},
                    Bool.pick(Method, String.eq(name, "textDocument/documentSymbol"), MSymbols{},
                      Bool.pick(Method, String.eq(name, "textDocument/completion"), MCompletion{},
                        Bool.pick(Method, String.eq(name, "textDocument/references"), MReferences{},
                          Bool.pick(Method, String.eq(name, "textDocument/rename"), MRename{},
                            Bool.pick(Method, String.eq(name, "textDocument/semanticTokens/full"), MSemantic{},
                              MOther{}))))))))))))))

# a method's role
def role(m: Method) -> Role:
  match m:
    case MInitialize{}:
      RRequest{}
    case MShutdown{}:
      RRequest{}
    case MExit{}:
      RExit{}
    case MOpen{}:
      RNotice{}
    case MChange{}:
      RNotice{}
    case MSave{}:
      RNotice{}
    case MClose{}:
      RNotice{}
    case MHover{}:
      RRequest{}
    case MDefinition{}:
      RRequest{}
    case MSymbols{}:
      RRequest{}
    case MCompletion{}:
      RRequest{}
    case MReferences{}:
      RRequest{}
    case MRename{}:
      RRequest{}
    case MSemantic{}:
      RRequest{}
    case MOther{}:
      RUnknown{}

# a message's method name, empty when it has none
def name_of(msg: J.Json) -> String:
  Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(msg, "method")), "")

# a message's id: null for a notification
def id_of(msg: J.Json) -> J.Json:
  Ezjson.get(msg, "id")

# the document a request is about
def uri_of(params: J.Json) -> String:
  Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(Ezjson.get(params, "textDocument"), "uri")), "")

# the text a didOpen carries: its document's, or none
def opened_text(params: J.Json) -> String:
  Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(Ezjson.get(params, "textDocument"), "text")), "")

# the text a didChange carries: its first content change's, which is the
# whole document (the server asks for full sync), or none
def changed_text(params: J.Json) -> String:
  Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(Ezjson.at(Ezjson.get(params, "contentChanges"), 0), "text")),
    "")

# the line of a request's position
def line_of(params: J.Json) -> U32:
  Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(Ezjson.get(params, "position"), "line")), 0)

# the character of a request's position
def col_of(params: J.Json) -> U32:
  Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(Ezjson.get(params, "position"), "character")), 0)

# a reply as the text sent
def text(r: Reply) -> String:
  match r:
    case RNote{body}:
      body
    case RResult{id, result}:
      Ezjson.print(Proto.response(id, result))
    case RError{id, code, message}:
      Ezjson.print(Proto.failure(id, code, message))

# notifications as replies
def notices(ns: List<&2, String>) -> List<&2, Reply>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      RNote{n} <> notices(t)

# the response to the request with this id
def respond(id: J.Json, a: Answer) -> Reply:
  match a:
    case Answer{result}:
      RResult{id, result}
    case Refusal{code, message}:
      RError{id, code, message}

# a request the server does not know is refused; a notification is ignored
def unknown(id: J.Json) -> List<&2, Reply>:
  match id:
    case J.JNull{}:
      []
    case other:
      [RError{other, "-32601", "method not found"}]

# the work of a request: its result, no notifications
def answered(result: J.Json, docs: List<&2, Docs.Doc>) -> Work:
  Work{[], Answer{result}, docs}

# the work of a notification: what it sends, and no answer
def noted(notes: List<&2, String>, docs: List<&2, Docs.Doc>) -> Work:
  Work{notes, Answer{J.JNull{}}, docs}

def step.go(r: Role, id: J.Json, w: Work) -> Out:
  match r:
    case RRequest{}:
      Work{notes, answer, docs} = w
      Out{[respond(id, answer)], False{}, docs}
    case RNotice{}:
      Work{notes, answer, docs} = w
      Out{notices(notes), False{}, docs}
    case RExit{}:
      Work{notes, answer, docs} = w
      Out{[], True{}, docs}
    case RUnknown{}:
      Work{notes, answer, docs} = w
      Out{unknown(id), False{}, docs}

# the dispatcher's decision for one message, whatever its method's work gave:
# a request gets one response with its id, a notification its notices, exit
# stops, and a method it does not know is refused or ignored
def step(m: Method, id: J.Json, w: Work) -> Out:
  step.go(role(m), id, w)

# publishing
# ----------
# What open, change, save and close publish is decided by the pure pub.*
# defs below, over what the IO gave them: the checker's errors (ds) and the
# texts of the document's bolt.bend candidates (rs). work only gathers those.

# a document's diagnostics, as the notification sent: the checker's errors,
# then the linter's findings
def pub.note(c: Enc.Cols, uri: String, ds: List<&2, Rep.Diag>, gs: List<&2, Finding.Graded>) -> String:
  Ezjson.print(Proto.publish(c, uri, ds, gs))

# the bolt.bend candidates of a document's path, nearest first: the ones the
# CLI reads for a file at that path, run from the same directory
def pub.cands(cwd: String, path: String) -> List<&2, String>:
  Config.chain(Config.home(cwd, Config.dir_of(path)))

# the linter's findings on the text the editor shows, each rule told the
# file's role among the marks, at the levels the nearest bolt.bend read gives
# them, less what the text's noqa comments
# silence, then the `noqa` rule's, which judges no project rule's code (the
# editor runs none); none for a bolt.bend, which is bolt's configuration,
# not source
def pub.lint(
  +path: String,
  +text: String,
  rs: List<&2, Maybe<&2, String>>,
  ms: List<&2, Role.Mark>
) -> List<&2, Finding.Graded>:
  +cfg = Config.nearest(rs)
  Bool.pick(List<&2, Finding.Graded>, Plan.is_config(path), [],
    Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
      Lint.graded(cfg, Lint.on.role(cfg, Role.of(ms, path), Src.of(path, text))), fs => Lint.graded(cfg, fs)))

# the role marks `bolt <path>` reads from a World: the imports of every file
# of the tree (Plan.graph), each file read for its imports alone
def pub.marks(+world: W.World) -> List<&2, Role.Mark>:
  Plan.marks.named(world)

# open or save: the checker's errors with the lint of the text, the errors
# kept for the changes after
def pub.checked(
  e: Enc.Enc,
  +uri: String,
  +text: String,
  +ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +ms: List<&2, Role.Mark>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  noted([pub.note(Enc.cols(e, text), uri, ds, pub.lint(Proto.path(uri), text, rs, ms))],
    Docs.set_checked(docs, uri, ds, ms))

# open: the document's text kept, then published with the checker's errors
def pub.open(
  e: Enc.Enc,
  +uri: String,
  +text: String,
  ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +ms: List<&2, Role.Mark>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  pub.checked(e, uri, text, ds, rs, ms, Docs.set(docs, uri, text))

# save: the text the editor shows published with the checker's new errors
def pub.save(
  e: Enc.Enc,
  +uri: String,
  ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +ms: List<&2, Role.Mark>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  pub.checked(e, uri, Maybe.default(&2, String, Docs.get(docs, uri), ""), ds, rs, ms, docs)

# change: the new text kept, and its lint published with the checker's last
# errors and the marks read with them
def pub.change(
  e: Enc.Enc,
  +uri: String,
  +text: String,
  rs: List<&2, Maybe<&2, String>>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  noted([pub.note(Enc.cols(e, text), uri, Docs.errors(docs, uri),
    pub.lint(Proto.path(uri), text, rs, Docs.marks(docs, uri)))], Docs.set(docs, uri, text))

# close: the document forgotten, and an empty list published
def pub.close(e: Enc.Enc, +uri: String, docs: List<&2, Docs.Doc>) -> Work:
  noted([pub.note(Enc.cols(e, ""), uri, [], [])], Docs.del(docs, uri))

# the texts of a document's bolt.bend candidates, as the files hold them
def pub.configs(~fs: F.Files, +uri: String) -> IO(List<&2, Maybe<&2, String>>):
  do IO<List<&2, Maybe<&2, String>>>:
    cwd : String <- F.cwd(fs)
    F.read_all(~fs, pub.cands(cwd, Proto.path(uri)))

# a file's text as an answer
def pub.read.answer(m: Maybe<&2, String>) -> W.Answer:
  match m:
    case None{}:
      W.Unread{}
    case Some{text}:
      W.Read{text}

# one question of the planner's, answered from the files: a directory's
# entries, or a file's text (a directory reads as no text)
def pub.answer(~fs: F.Files, ask: W.Ask) -> IO(W.Answer):
  match ask:
    case W.Entries{dir}:
      do IO<W.Answer>:
        es : List<&2, String> <- F.entries(fs, dir)
        return W.Listed{es}
    case W.Contents{path}:
      do IO<W.Answer>:
        m : Maybe<&2, String> <- F.read(fs, path)
        return pub.read.answer(m)

# every question answered, in order
def pub.answers(~fs: F.Files, asks: List<&2, W.Ask>) -> IO(List<&2, W.Reply>):
  match asks:
    case Nil{}:
      IO.pure(List<&2, W.Reply>, [])
    case Con{+a, rest}:
      do IO<List<&2, W.Reply>>:
        r : W.Answer <- pub.answer(~fs, a)
        more : List<&2, W.Reply> <- pub.answers(~fs, rest)
        return W.Reply{a, r} <> more

# the World with more answers in it
def pub.world.more(world: W.World, rs: List<&2, W.Reply>) -> W.World:
  W.World{paths, cwd, replies} = world
  W.World{paths, cwd, List.append(&2, W.Reply, replies, rs)}

# the planner's questions answered and the World gone round again, or the
# World as it is once the planner asks none
def pub.world.step(
  ~fs: F.Files,
  asks: List<&2, W.Ask>,
  +world: W.World,
  go: W.World -> IO(W.World)
) -> IO(W.World):
  match asks:
    case Nil{}:
      IO.pure(W.World, world)
    case Con{a, rest}:
      do IO<W.World>:
        rs : List<&2, W.Reply> <- pub.answers(~fs, a <> rest)
        go(pub.world.more(world, rs))

# the World `bolt <path>` reads, gathered as src/lint.bend gathers it: the
# planner's questions answered until it asks none, under the same fuel
def pub.world.go(~fs: F.Files, fuel: Nat, +world: W.World) -> IO(W.World):
  match fuel:
    case 0n:
      IO.pure(W.World, world)
    case 1n+f:
      pub.world.step(~fs, Plan.wants(world), world, w => pub.world.go(~fs, f, w))

# the role marks the tree's imports give a document, as `bolt <path>` reads
# them
def pub.seen(~fs: F.Files, +uri: String) -> IO(List<&2, Role.Mark>):
  do IO<List<&2, Role.Mark>>:
    cwd : String <- F.cwd(fs)
    w : W.World <- pub.world.go(~fs, Nat.add(Plan.limit(), 2n), W.World{[Proto.path(uri)], cwd, []})
    return pub.marks(w)

# open, on the checker's run on the file on disk
def pub.opened(
  ~fs: F.Files,
  ~ck: C.Checker,
  e: Enc.Enc,
  +uri: String,
  text: String,
  docs: List<&2, Docs.Doc>
) -> IO(Work):
  do IO<Work>:
    a : C.Answer <- C.check(ck, Proto.path(uri))
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    ms : List<&2, Role.Mark> <- pub.seen(~fs, uri)
    return pub.open(e, uri, text, C.errors(a), rs, ms, docs)

# save, on the checker's run on the file on disk
def pub.saved(~fs: F.Files, ~ck: C.Checker, e: Enc.Enc, +uri: String, docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    a : C.Answer <- C.check(ck, Proto.path(uri))
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    ms : List<&2, Role.Mark> <- pub.seen(~fs, uri)
    return pub.save(e, uri, C.errors(a), rs, ms, docs)

# change: the linter only
def pub.changed(~fs: F.Files, e: Enc.Enc, +uri: String, text: String, docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    return pub.change(e, uri, text, rs, docs)

def hover.of(m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.hover(item)
    case Some{Nav.Here{uri, b}}:
      Proto.hover.local(b)

def definition.of(c: Enc.Cols, m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.location(c, uri, item)
    case Some{Nav.Here{uri, b}}:
      Proto.location.local(c, uri, b)

# the column a request's position names, read in the negotiated encoding of
# the document's text
def col_in(c: Enc.Cols, +params: J.Json) -> U32:
  Enc.into(c, line_of(params), col_of(params))

# hover at a request's position
def hovered(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  e: Enc.Enc,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +params: J.Json
) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    f : Maybe<&2, Nav.Found> <- Nav.hover(~fs, docs, uri, line_of(params), col_in(Enc.cols(e, text), params))
    return answered(hover.of(f), docs)

# definition at a request's position
def defined(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  e: Enc.Enc,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +params: J.Json
) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +c : Enc.Cols = Enc.cols(e, text)
    f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri, line_of(params), col_in(c, params))
    return answered(definition.of(c, f), docs)

def complete.with(
  ~fs: F.Files,
  c: Enc.Cols,
  +prefix: String,
  +docs: List<&2, Docs.Doc>,
  uri: String,
  +line: U32,
  +col: U32
) -> IO(Work):
  do IO<Work>:
    items : List<&2, Outline.Item> <- Nav.candidates(~fs, docs, uri, prefix, line)
    return answered(Proto.completions(c, items, line, (col - U32.from_nat(String.length(prefix)) : U32), col), docs)

# the candidates for the name being typed at a position
def complete(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  e: Enc.Enc,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +params: J.Json
) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +c : Enc.Cols = Enc.cols(e, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(c, params)
    complete.with(~fs, c, Word.before(text, line, col), docs, uri, line, col)

def references.of(c: Enc.Cols, s: Nav.Sites, uri: String, name: String) -> J.Json:
  Nav.Sites{mine, at} = s
  Proto.locations(c, uri, name, at)

# only a name bound in the document renames; the editor shows the refusal
def rename.of(c: Enc.Cols, s: Nav.Sites, uri: String, name: String, new: String) -> Answer:
  Nav.Sites{mine, at} = s
  match mine:
    case True{}:
      Answer{Proto.rename(c, uri, name, new, at)}
    case False{}:
      Refusal{"-32803", "only a name bound in this file can be renamed"}

# every position of the name at a position
def references(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  e: Enc.Enc,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +params: J.Json
) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +c : Enc.Cols = Enc.cols(e, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(c, params)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return answered(references.of(c, s, uri, Word.at(text, line, col)), docs)

# the edit renaming the name at a position, or a refusal
def renamed(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  e: Enc.Enc,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +params: J.Json
) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +c : Enc.Cols = Enc.cols(e, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(c, params)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return Work{[],
      rename.of(c, s, uri, Word.at(text, line, col),
        Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(params, "newName")), "")),
      docs}

# the document's semantic tokens
def semantic(~fs: F.Files, e: Enc.Enc, +docs: List<&2, Docs.Doc>, uri: String) -> IO(Work):  # noqa: L001 LSP IO glue
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    return answered(Proto.semantic(Semantic.data(e, text)), docs)

# the document's symbols
def symbols(~fs: F.Files, e: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String) -> IO(Work):  # noqa: L001 LSP IO glue
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    items : List<&2, Outline.Item> <- Nav.outline(~fs, docs, uri)
    return answered(Proto.symbols(Enc.cols(e, text), items), docs)

# the work behind a method: what the checker, the files and the documents
# give it. It does not see the message's id: step alone puts that on a reply
def work(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  ~ck: C.Checker,
  enc: Enc.Enc,
  m: Method,
  +params: J.Json,
  +docs: List<&2, Docs.Doc>
) -> IO(Work):
  match m:
    case MInitialize{}:
      IO.pure(Work, answered(Proto.capabilities(enc), docs))
    case MShutdown{}:
      IO.pure(Work, answered(J.JNull{}, docs))
    case MExit{}:
      IO.pure(Work, noted([], docs))
    case MOpen{}:
      pub.opened(~fs, ~ck, enc, uri_of(params), opened_text(params), docs)
    case MChange{}:
      pub.changed(~fs, enc, uri_of(params), changed_text(params), docs)
    case MSave{}:
      pub.saved(~fs, ~ck, enc, uri_of(params), docs)
    case MClose{}:
      IO.pure(Work, pub.close(enc, uri_of(params), docs))
    case MHover{}:
      hovered(~fs, enc, docs, uri_of(params), params)
    case MDefinition{}:
      defined(~fs, enc, docs, uri_of(params), params)
    case MSymbols{}:
      symbols(~fs, enc, docs, uri_of(params))
    case MCompletion{}:
      complete(~fs, enc, docs, uri_of(params), params)
    case MReferences{}:
      references(~fs, enc, docs, uri_of(params), params)
    case MRename{}:
      renamed(~fs, enc, docs, uri_of(params), params)
    case MSemantic{}:
      semantic(~fs, enc, docs, uri_of(params))
    case MOther{}:
      IO.pure(Work, noted([], docs))

# the encoding after a message: initialize settles it (enc.bend's
# negotiate); every other message keeps it
def encoding(m: Method, params: J.Json, e: Enc.Enc) -> Enc.Enc:
  match m:
    case MInitialize{}:
      Enc.negotiate(params)
    case _other:
      e

# the encoding after a message, read off the message itself: its method, and
# its `params` member for initialize to negotiate from
def encoding.of(+msg: J.Json, e: Enc.Enc) -> Enc.Enc:
  encoding(method(name_of(msg)), Ezjson.get(msg, "params"), e)

# one message: its method's work, then step's decision on it
def handle(  # noqa: L001 LSP IO glue
  ~fs: F.Files,
  ~ck: C.Checker,
  e: Enc.Enc,
  +msg: J.Json,
  docs: List<&2, Docs.Doc>
) -> IO(Out):
  +m = method(name_of(msg))
  do IO<Out>:
    w : Work <- work(~fs, ~ck, e, m, Ezjson.get(msg, "params"), docs)
    return step(m, id_of(msg), w)

# a parsed message, or null when it did not parse
def decoded(m: Maybe<&2, J.Json>) -> J.Json:
  Maybe.default(&2, J.Json, m, J.JNull{})

# every reply sent, in order
def send_all(~H: Type, ~tr: T.Transport<H>, replies: List<&2, Reply>, h3: H) -> IO(H):  # noqa: L001 serve loop IO
  match replies:
    case Nil{}:
      IO.pure(H, h3)
    case Con{body, t}:
      do IO<H>:
        h2 : H <- T.send(H, tr, h3, text(body))
        send_all(~H, ~tr, t, h2)

# the loop goes on with the documents, unless the message said to quit
def next(  # noqa: L001 serve loop IO
  -H: Type,
  quit: Bool,
  h3: H,
  e: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h3, e, docs)

# the replies sent, then the loop goes on
def answer(  # noqa: L001 serve loop IO
  ~H: Type,
  ~tr: T.Transport<H>,
  out: Out,
  h3: H,
  e: Enc.Enc,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  Out{replies, quit, docs} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h3)
    next(H, quit, h2, e, docs, rest)

# a message handled under the encoding it leaves, and answered
def turn.msg(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  ~ck: C.Checker,
  +msg: J.Json,
  h3: H,
  e: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  +e2 = encoding.of(msg, e)
  do IO<Unit>:
    out : Out <- handle(~fs, ~ck, e2, msg, docs)
    answer(~H, ~tr, out, h3, e2, rest)

# one message body handled and answered; none means the peer is gone
def turn(  # noqa: L001 serve loop IO
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  ~ck: C.Checker,
  m: Maybe<&2, String>,
  h3: H,
  e: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      turn.msg(~H, ~tr, ~fs, ~ck, decoded(Ezjson.parse(body)), h3, e, docs, rest)

# what recv gave: the handle and maybe a body
def got(  # noqa: L001 serve loop IO
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  ~ck: C.Checker,
  r: H & Maybe<&2, String>,
  e: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  (h, m) = r
  turn(~H, ~tr, ~fs, ~ck, m, h, e, docs, rest)

def serve.go(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  ~ck: C.Checker,
  fuel: Nat,
  h3: H,
  e: Enc.Enc,
  docs: List<&2, Docs.Doc>
) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        r : H & Maybe<&2, String> <- T.recv(H, tr, h3)
        got(~H, ~tr, ~fs, ~ck, r, e, docs, h => e2 => d => serve.go(~H, ~tr, ~fs, ~ck, f, h, e2, d))

# serves until exit, the peer's end, or the fuel's (a message each), in
# UTF-16 until initialize negotiates
def serve(  # noqa: L001 serve loop IO
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  ~ck: C.Checker,
  fuel: Nat,
  h3: H,
  docs: List<&2, Docs.Doc>
) -> IO(Unit):
  serve.go(~H, ~tr, ~fs, ~ck, fuel, h3, Enc.Utf16{}, docs)
