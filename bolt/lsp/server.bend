# lsp/server: the loop. The transport the messages ride on and the files
# behind imports and Base are passed in (transport/, files/); the checker
# behind the diagnostics is checker/bend.bend, called directly. The open documents are the
# loop's state. The checker runs on open and save, against the file on disk;
# the linter on every open, change and save, on the text the editor shows.
import Base
import 0xd9c8d4d2899ddda845dfa7525a3568ea/main.bend as Ezjson
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J
import ./proto.bend as Proto
import ./docs.bend as Docs
import ./nav.bend as Nav
import ./semantic.bend as Semantic
import ../rules.bend as Lint
import ../finding.bend as Finding
import ../config.bend as Config
import ../lint/plan.bend as Plan
import ./transport/service.bend as T
import ./checker/answer.bend as C
import ./checker/bend.bend as BendChecker
import ./files/service.bend as F
import ./report.bend as Rep
import ./enc.bend as Enc
import ../../syntax/outline.bend as Outline
import ../../syntax/word.bend as Word

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
def role(mm: Method) -> Role:
  match mm:
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

# the line of a request's position
def line_of(params: J.Json) -> U32:
  Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(Ezjson.get(params, "position"), "line")), 0)

# the character of a request's position
def col_of(params: J.Json) -> U32:
  Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(Ezjson.get(params, "position"), "character")), 0)

# a reply as the text sent
def text(rr: Reply) -> String:
  match rr:
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
def respond(id: J.Json, aa: Answer) -> Reply:
  match aa:
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

def step.go(rr: Role, id: J.Json, ww: Work) -> Out:
  match rr:
    case RRequest{}:
      Work{notes, answer, docs} = ww
      Out{[respond(id, answer)], False{}, docs}
    case RNotice{}:
      Work{notes, answer, docs} = ww
      Out{notices(notes), False{}, docs}
    case RExit{}:
      Work{notes, answer, docs} = ww
      Out{[], True{}, docs}
    case RUnknown{}:
      Work{notes, answer, docs} = ww
      Out{unknown(id), False{}, docs}

# the dispatcher's decision for one message, whatever its method's work gave:
# a request gets one response with its id, a notification its notices, exit
# stops, and a method it does not know is refused or ignored
def step(mm: Method, id: J.Json, ww: Work) -> Out:
  step.go(role(mm), id, ww)

# publishing
# ----------
# What open, change, save and close publish is decided by the pure pub.*
# defs below, over what the IO gave them: the checker's errors (ds) and the
# texts of the document's bolt.bend candidates (rs). work only gathers those.

# a document's diagnostics, as the notification sent: the checker's errors,
# then the linter's findings
def pub.note(cc: Enc.Cols, uri: String, ds: List<&2, Rep.Diag>, gs: List<&2, Finding.Graded>) -> String:
  Ezjson.print(Proto.publish(cc, uri, ds, gs))

# the bolt.bend candidates of a document's path, nearest first: the ones the
# CLI reads for a file at that path, run from the same directory
def pub.cands(cwd: String, path: String) -> List<&2, String>:
  Config.chain(Config.home(cwd, Config.dir_of(path)))

# the linter's findings on the text the editor shows, at the levels the
# nearest bolt.bend read gives them; none for a bolt.bend, which is bolt's
# configuration, not source
def pub.lint(+path: String, +text: String, rs: List<&2, Maybe<&2, String>>) -> List<&2, Finding.Graded>:
  Bool.pick(List<&2, Finding.Graded>, Plan.is_config(path), [], Lint.graded(Config.nearest(rs), Lint.all(path, text)))

# open or save: the checker's errors with the lint of the text, the errors
# kept for the changes after
def pub.checked(
  ee: Enc.Enc,
  +uri: String,
  +text: String,
  +ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  noted([pub.note(Enc.cols(ee, text), uri, ds, pub.lint(Proto.path(uri), text, rs))], Docs.set_errors(docs, uri, ds))

# open: the document's text kept, then published with the checker's errors
def pub.open(
  ee: Enc.Enc,
  +uri: String,
  +text: String,
  ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  pub.checked(ee, uri, text, ds, rs, Docs.set(docs, uri, text))

# save: the text the editor shows published with the checker's new errors
def pub.save(
  ee: Enc.Enc,
  +uri: String,
  ds: List<&2, Rep.Diag>,
  rs: List<&2, Maybe<&2, String>>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  pub.checked(ee, uri, Maybe.default(&2, String, Docs.get(docs, uri), ""), ds, rs, docs)

# change: the new text kept, and its lint published with the checker's last
# errors
def pub.change(
  ee: Enc.Enc,
  +uri: String,
  +text: String,
  rs: List<&2, Maybe<&2, String>>,
  +docs: List<&2, Docs.Doc>
) -> Work:
  noted([pub.note(Enc.cols(ee, text), uri, Docs.errors(docs, uri), pub.lint(Proto.path(uri), text, rs))],
    Docs.set(docs, uri, text))

# close: the document forgotten, and an empty list published
def pub.close(ee: Enc.Enc, +uri: String, docs: List<&2, Docs.Doc>) -> Work:
  noted([pub.note(Enc.cols(ee, ""), uri, [], [])], Docs.del(docs, uri))

# the texts of a document's bolt.bend candidates, as the files hold them
def pub.configs(~fs: F.Files, +uri: String) -> IO(List<&2, Maybe<&2, String>>):
  do IO<List<&2, Maybe<&2, String>>>:
    cwd : String <- F.cwd(fs)
    F.read_all(~fs, pub.cands(cwd, Proto.path(uri)))

# open, on the checker's run on the file on disk
def pub.opened(
  ~fs: F.Files,
  ee: Enc.Enc,
  +uri: String,
  text: String,
  docs: List<&2, Docs.Doc>
) -> IO(Work):
  do IO<Work>:
    aa : C.Answer <- BendChecker.check(Proto.path(uri))
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    return pub.open(ee, uri, text, C.errors(aa), rs, docs)

# save, on the checker's run on the file on disk
def pub.saved(~fs: F.Files, ee: Enc.Enc, +uri: String, docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    aa : C.Answer <- BendChecker.check(Proto.path(uri))
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    return pub.save(ee, uri, C.errors(aa), rs, docs)

# change: the linter only
def pub.changed(~fs: F.Files, ee: Enc.Enc, +uri: String, text: String, docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    rs : List<&2, Maybe<&2, String>> <- pub.configs(~fs, uri)
    return pub.change(ee, uri, text, rs, docs)

def hover.of(mm: Maybe<&2, Nav.Found>) -> J.Json:
  match mm:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.hover(item)
    case Some{Nav.Here{uri, b}}:
      Proto.hover.local(b)

def definition.of(cc: Enc.Cols, mm: Maybe<&2, Nav.Found>) -> J.Json:
  match mm:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.location(cc, uri, item)
    case Some{Nav.Here{uri, b}}:
      Proto.location.local(cc, uri, b)

# the column a request's position names, read in the negotiated encoding of
# the document's text
def col_in(cc: Enc.Cols, +params: J.Json) -> U32:
  Enc.into(cc, line_of(params), col_of(params))

# hover at a request's position
def hovered(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String, +params: J.Json) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    f : Maybe<&2, Nav.Found> <- Nav.hover(~fs, docs, uri, line_of(params), col_in(Enc.cols(ee, text), params))
    return answered(hover.of(f), docs)

# definition at a request's position
def defined(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String, +params: J.Json) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +cc : Enc.Cols = Enc.cols(ee, text)
    f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri, line_of(params), col_in(cc, params))
    return answered(definition.of(cc, f), docs)

def complete.with(
  ~fs: F.Files,
  cc: Enc.Cols,
  +prefix: String,
  +docs: List<&2, Docs.Doc>,
  uri: String,
  +line: U32,
  +col: U32
) -> IO(Work):
  do IO<Work>:
    items : List<&2, Outline.Item> <- Nav.candidates(~fs, docs, uri, prefix, line)
    return answered(Proto.completions(cc, items, line, (col - U32.from_nat(String.length(prefix)) : U32), col), docs)

# the candidates for the name being typed at a position
def complete(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String, +params: J.Json) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +cc : Enc.Cols = Enc.cols(ee, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(cc, params)
    complete.with(~fs, cc, Word.before(text, line, col), docs, uri, line, col)

def references.of(cc: Enc.Cols, ss: Nav.Sites, uri: String, name: String) -> J.Json:
  Nav.Sites{mine, at} = ss
  Proto.locations(cc, uri, name, at)

# only a name bound in the document renames; the editor shows the refusal
def rename.of(cc: Enc.Cols, ss: Nav.Sites, uri: String, name: String, new: String) -> Answer:
  Nav.Sites{mine, at} = ss
  match mine:
    case True{}:
      Answer{Proto.rename(cc, uri, name, new, at)}
    case False{}:
      Refusal{"-32803", "only a name bound in this file can be renamed"}

# every position of the name at a position
def references(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String, +params: J.Json) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +cc : Enc.Cols = Enc.cols(ee, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(cc, params)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return answered(references.of(cc, s, uri, Word.at(text, line, col)), docs)

# the edit renaming the name at a position, or a refusal
def renamed(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String, +params: J.Json) -> IO(Work):
  do IO<Work>:
    +text : String <- Nav.text_of(~fs, docs, uri)
    +cc : Enc.Cols = Enc.cols(ee, text)
    +line : U32 = line_of(params)
    +col : U32 = col_in(cc, params)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return Work{[],
      rename.of(cc, s, uri, Word.at(text, line, col),
        Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(params, "newName")), "")),
      docs}

# the document's semantic tokens
def semantic(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, uri: String) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    return answered(Proto.semantic(Semantic.data(ee, text)), docs)

# the document's symbols
def symbols(~fs: F.Files, ee: Enc.Enc, +docs: List<&2, Docs.Doc>, +uri: String) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    items : List<&2, Outline.Item> <- Nav.outline(~fs, docs, uri)
    return answered(Proto.symbols(Enc.cols(ee, text), items), docs)

# the work behind a method: what the checker, the files and the documents
# give it. It does not see the message's id: step alone puts that on a reply
def work(
  ~fs: F.Files,
  ee: Enc.Enc,
  mm: Method,
  +params: J.Json,
  +docs: List<&2, Docs.Doc>
) -> IO(Work):
  match mm:
    case MInitialize{}:
      IO.pure(Work, answered(Proto.capabilities(ee), docs))
    case MShutdown{}:
      IO.pure(Work, answered(J.JNull{}, docs))
    case MExit{}:
      IO.pure(Work, noted([], docs))
    case MOpen{}:
      pub.opened(~fs, ee, uri_of(params),
        Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(Ezjson.get(params, "textDocument"), "text")), ""), docs)
    case MChange{}:
      pub.changed(~fs, ee, uri_of(params),
        Maybe.default(&2, String, Ezjson.as_str(Ezjson.get(Ezjson.at(Ezjson.get(params, "contentChanges"), 0), "text")), ""), docs)
    case MSave{}:
      pub.saved(~fs, ee, uri_of(params), docs)
    case MClose{}:
      IO.pure(Work, pub.close(ee, uri_of(params), docs))
    case MHover{}:
      hovered(~fs, ee, docs, uri_of(params), params)
    case MDefinition{}:
      defined(~fs, ee, docs, uri_of(params), params)
    case MSymbols{}:
      symbols(~fs, ee, docs, uri_of(params))
    case MCompletion{}:
      complete(~fs, ee, docs, uri_of(params), params)
    case MReferences{}:
      references(~fs, ee, docs, uri_of(params), params)
    case MRename{}:
      renamed(~fs, ee, docs, uri_of(params), params)
    case MSemantic{}:
      semantic(~fs, ee, docs, uri_of(params))
    case MOther{}:
      IO.pure(Work, noted([], docs))

# the encoding after a message: initialize settles it (enc.bend's
# negotiate); every other message keeps it
def encoding(mm: Method, params: J.Json, ee: Enc.Enc) -> Enc.Enc:
  match mm:
    case MInitialize{}:
      Enc.negotiate(params)
    case _other:
      ee

# one message: its method's work, then step's decision on it
def handle(~fs: F.Files, ee: Enc.Enc, +msg: J.Json, docs: List<&2, Docs.Doc>) -> IO(Out):
  +mm = method(name_of(msg))
  do IO<Out>:
    w : Work <- work(~fs, ee, mm, Ezjson.get(msg, "params"), docs)
    return step(mm, id_of(msg), w)

# a parsed message, or null when it did not parse
def decoded(mm: Maybe<&2, J.Json>) -> J.Json:
  Maybe.default(&2, J.Json, mm, J.JNull{})

# every reply sent, in order
def send_all(~H: Type, ~tr: T.Transport<H>, replies: List<&2, Reply>, h3: H) -> IO(H):
  match replies:
    case Nil{}:
      IO.pure(H, h3)
    case Con{body, t}:
      do IO<H>:
        h2 : H <- T.send(H, tr, h3, text(body))
        send_all(~H, ~tr, t, h2)

# the loop goes on with the documents, unless the message said to quit
def next(
  -H: Type,
  quit: Bool,
  h3: H,
  ee: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h3, ee, docs)

# the replies sent, then the loop goes on
def answer(
  ~H: Type,
  ~tr: T.Transport<H>,
  out: Out,
  h3: H,
  ee: Enc.Enc,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  Out{replies, quit, docs} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h3)
    next(H, quit, h2, ee, docs, rest)

# a message handled under the encoding it leaves, and answered
def turn.msg(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  +msg: J.Json,
  h3: H,
  ee: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  +e2 = encoding(method(name_of(msg)), Ezjson.get(msg, "params"), ee)
  do IO<Unit>:
    out : Out <- handle(~fs, e2, msg, docs)
    answer(~H, ~tr, out, h3, e2, rest)

# one message body handled and answered; none means the peer is gone
def turn(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  mm: Maybe<&2, String>,
  h3: H,
  ee: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match mm:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      turn.msg(~H, ~tr, ~fs, decoded(Ezjson.parse(body)), h3, ee, docs, rest)

# what recv gave: the handle and maybe a body
def got(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  rr: H & Maybe<&2, String>,
  ee: Enc.Enc,
  docs: List<&2, Docs.Doc>,
  rest: H -> Enc.Enc -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  (h, m) = rr
  turn(~H, ~tr, ~fs, m, h, ee, docs, rest)

def serve.go(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  fuel: Nat,
  h3: H,
  ee: Enc.Enc,
  docs: List<&2, Docs.Doc>
) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        r : H & Maybe<&2, String> <- T.recv(H, tr, h3)
        got(~H, ~tr, ~fs, r, ee, docs, hh => e2 => dd => serve.go(~H, ~tr, ~fs, f, hh, e2, dd))

# serves until exit, the peer's end, or the fuel's (a message each), in
# UTF-16 until initialize negotiates
def serve(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~fs: F.Files,
  fuel: Nat,
  h3: H,
  docs: List<&2, Docs.Doc>
) -> IO(Unit):
  serve.go(~H, ~tr, ~fs, fuel, h3, Enc.Utf16{}, docs)
