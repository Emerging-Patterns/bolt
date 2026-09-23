# lsp/server: the loop. Everything outside the process is an injected core
# service: the transport the messages ride on, the checker behind the
# diagnostics, the files behind imports and Base. The open documents are the
# loop's state. Diagnostics run on open and save, against the file on disk.
import Base
import 0xa3c2445eb44c5d8406e6229be518fccb/value.bend as J
import 0xa3c2445eb44c5d8406e6229be518fccb/parse.bend as Parse
import 0xa3c2445eb44c5d8406e6229be518fccb/print.bend as Print
import ./proto.bend as Proto
import ./docs.bend as Docs
import ./nav.bend as Nav
import ./semantic.bend as Semantic
import ../rules.bend as Lint
import ../finding.bend as Finding
import ../config.bend as Config
import ./transport/service.bend as T
import ./checker/service.bend as C
import ./files/service.bend as F
import ./report.bend as Rep
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
  J.str_or(J.get(msg, "method"), "")

# a message's id: null for a notification
def id_of(msg: J.Json) -> J.Json:
  J.get(msg, "id")

# the document a request is about
def uri_of(params: J.Json) -> String:
  J.str_or(J.get(J.get(params, "textDocument"), "uri"), "")

# the line of a request's position
def line_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "line"), 0)

# the character of a request's position
def col_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "character"), 0)

# a reply as the text sent
def text(rr: Reply) -> String:
  match rr:
    case RNote{body}:
      body
    case RResult{id, result}:
      Print.print(Proto.response(id, result))
    case RError{id, code, message}:
      Print.print(Proto.failure(id, code, message))

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

# a bolt.bend is bolt's configuration, not source to lint
def is_config(+path: String) -> Bool:
  Bool.or(String.eq(path, "bolt.bend"), String.ends_with(path, "/bolt.bend"))

# the linter's findings on the text the editor shows, at the levels the
# nearest bolt.bend gives them
def linted(~fs: F.Files, +uri: String, +docs: List<&2, Docs.Doc>) -> IO(List<&2, Finding.Graded>):
  +path = Proto.path(uri)
  do IO<List<&2, Finding.Graded>>:
    rs : List<&2, Maybe<&2, String>> <- F.read_all(~fs, Config.candidates(64n, Config.dir_of(path)))
    return Bool.pick(List<&2, Finding.Graded>, is_config(path), [],
      Lint.graded(Config.nearest(rs), Lint.all(path, Maybe.default(&2, String, Docs.get(docs, uri), ""))))

# the checker's errors and the linter's findings published for a document
def published(~fs: F.Files, +uri: String, +docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    gs : List<&2, Finding.Graded> <- linted(~fs, uri, docs)
    return noted([Print.print(Proto.publish(uri, Docs.errors(docs, uri), gs))], docs)

# diagnostics for a document, the checker run (on the file on disk) and the
# linter (on the text)
def checked(~fs: F.Files, +uri: String, ck: C.Checker, +docs: List<&2, Docs.Doc>) -> IO(Work):
  do IO<Work>:
    ds : List<&2, Rep.Diag> <- C.check(ck, Proto.path(uri))
    published(~fs, uri, Docs.set_errors(docs, uri, ds))

def hover.of(mm: Maybe<&2, Nav.Found>) -> J.Json:
  match mm:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.hover(item)
    case Some{Nav.Here{uri, b}}:
      Proto.hover.local(b)

def definition.of(mm: Maybe<&2, Nav.Found>) -> J.Json:
  match mm:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.location(uri, item)
    case Some{Nav.Here{uri, b}}:
      Proto.location.local(uri, b)

def complete.with(
  ~fs: F.Files,
  +prefix: String,
  +docs: List<&2, Docs.Doc>,
  uri: String,
  +line: U32,
  +col: U32
) -> IO(Work):
  do IO<Work>:
    items : List<&2, Outline.Item> <- Nav.candidates(~fs, docs, uri, prefix, line)
    return answered(Proto.completions(items, line, (col - U32.from_nat(String.length(prefix)) : U32), col), docs)

# the candidates for the name being typed at a position
def complete(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, +line: U32, +col: U32) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    complete.with(~fs, Word.before(text, line, col), docs, uri, line, col)

def references.of(ss: Nav.Sites, uri: String, name: String) -> J.Json:
  Nav.Sites{mine, at} = ss
  Proto.locations(uri, name, at)

# only a name bound in the document renames; the editor shows the refusal
def rename.of(ss: Nav.Sites, uri: String, name: String, new: String) -> Answer:
  Nav.Sites{mine, at} = ss
  match mine:
    case True{}:
      Answer{Proto.rename(uri, name, new, at)}
    case False{}:
      Refusal{"-32803", "only a name bound in this file can be renamed"}

# every position of the name at a position
def references(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, +line: U32, +col: U32) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return answered(references.of(s, uri, Word.at(text, line, col)), docs)

# the edit renaming the name at a position, or a refusal
def renamed(
  ~fs: F.Files,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  +line: U32,
  +col: U32,
  new: String
) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return Work{[], rename.of(s, uri, Word.at(text, line, col), new), docs}

# the document's semantic tokens
def semantic(~fs: F.Files, +docs: List<&2, Docs.Doc>, uri: String) -> IO(Work):
  do IO<Work>:
    text : String <- Nav.text_of(~fs, docs, uri)
    return answered(Proto.semantic(Semantic.data(text)), docs)

# the work behind a method: what the checker, the files and the documents
# give it. It does not see the message's id: step alone puts that on a reply
def work(
  ~ck: C.Checker,
  ~fs: F.Files,
  mm: Method,
  +params: J.Json,
  +docs: List<&2, Docs.Doc>
) -> IO(Work):
  match mm:
    case MInitialize{}:
      IO.pure(Work, answered(Proto.capabilities(), docs))
    case MShutdown{}:
      IO.pure(Work, answered(J.JNull{}, docs))
    case MExit{}:
      IO.pure(Work, noted([], docs))
    case MOpen{}:
      checked(~fs, uri_of(params), ck,
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.get(params, "textDocument"), "text"), "")))
    case MChange{}:
      published(~fs, uri_of(params),
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.first(J.get(params, "contentChanges")), "text"), "")))
    case MSave{}:
      checked(~fs, uri_of(params), ck, docs)
    case MClose{}:
      IO.pure(Work, noted([Print.print(Proto.publish(uri_of(params), [], []))], Docs.del(docs, uri_of(params))))
    case MHover{}:
      do IO<Work>:
        f : Maybe<&2, Nav.Found> <- Nav.hover(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return answered(hover.of(f), docs)
    case MDefinition{}:
      do IO<Work>:
        f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return answered(definition.of(f), docs)
    case MSymbols{}:
      do IO<Work>:
        items : List<&2, Outline.Item> <- Nav.outline(~fs, docs, uri_of(params))
        return answered(Proto.symbols(items), docs)
    case MCompletion{}:
      complete(~fs, docs, uri_of(params), line_of(params), col_of(params))
    case MReferences{}:
      references(~fs, docs, uri_of(params), line_of(params), col_of(params))
    case MRename{}:
      renamed(~fs, docs, uri_of(params), line_of(params), col_of(params), J.str_or(J.get(params, "newName"), ""))
    case MSemantic{}:
      semantic(~fs, docs, uri_of(params))
    case MOther{}:
      IO.pure(Work, noted([], docs))

# one message: its method's work, then step's decision on it
def handle(~ck: C.Checker, ~fs: F.Files, +msg: J.Json, docs: List<&2, Docs.Doc>) -> IO(Out):
  +mm = method(name_of(msg))
  do IO<Out>:
    w : Work <- work(~ck, ~fs, mm, J.get(msg, "params"), docs)
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
  docs: List<&2, Docs.Doc>,
  rest: H -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h3, docs)

# the replies sent, then the loop goes on
def answer(~H: Type, ~tr: T.Transport<H>, out: Out, h3: H, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  Out{replies, quit, docs} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h3)
    next(H, quit, h2, docs, rest)

# one message body handled and answered; none means the peer is gone
def turn(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~ck: C.Checker,
  ~fs: F.Files,
  mm: Maybe<&2, String>,
  h3: H,
  docs: List<&2, Docs.Doc>,
  rest: H -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  match mm:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      do IO<Unit>:
        out : Out <- handle(~ck, ~fs, decoded(Parse.parse(body)), docs)
        answer(~H, ~tr, out, h3, rest)

# what recv gave: the handle and maybe a body
def got(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~ck: C.Checker,
  ~fs: F.Files,
  rr: H & Maybe<&2, String>,
  docs: List<&2, Docs.Doc>,
  rest: H -> List<&2, Docs.Doc> -> IO(Unit)
) -> IO(Unit):
  (h, m) = rr
  turn(~H, ~tr, ~ck, ~fs, m, h, docs, rest)

# serves until exit, the peer's end, or the fuel's (a message each)
def serve(
  ~H: Type,
  ~tr: T.Transport<H>,
  ~ck: C.Checker,
  ~fs: F.Files,
  fuel: Nat,
  h3: H,
  docs: List<&2, Docs.Doc>
) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        r : H & Maybe<&2, String> <- T.recv(H, tr, h3)
        got(~H, ~tr, ~ck, ~fs, r, docs, hh => dd => serve(~H, ~tr, ~ck, ~fs, f, hh, dd))
