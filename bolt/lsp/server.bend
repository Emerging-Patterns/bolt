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

# what one message leads to: the bodies to send, whether to stop, the documents
type Out is Data:
  Out{replies: List<&2, String>, quit: Bool, docs: List<&2, Docs.Doc>}

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

# the document a request is about
def uri_of(params: J.Json) -> String:
  J.str_or(J.get(J.get(params, "textDocument"), "uri"), "")

# the line of a request's position
def line_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "line"), 0)

# the character of a request's position
def col_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "character"), 0)

# one reply body
def reply(id: J.Json, result: J.Json) -> List<&2, String>:
  [Print.print(Proto.response(id, result))]

# a request the server does not know is refused; a notification is ignored
def unknown(id: J.Json) -> List<&2, String>:
  match id:
    case J.JNull{}:
      []
    case other:
      [Print.print(Proto.failure(other, "-32601", "method not found"))]

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
def published(~fs: F.Files, +uri: String, +docs: List<&2, Docs.Doc>) -> IO(Out):
  do IO<Out>:
    gs : List<&2, Finding.Graded> <- linted(~fs, uri, docs)
    return Out{[Print.print(Proto.publish(uri, Docs.errors(docs, uri), gs))], False{}, docs}

# diagnostics for a document, the checker run (on the file on disk) and the
# linter (on the text)
def checked(~fs: F.Files, +uri: String, ck: C.Checker, +docs: List<&2, Docs.Doc>) -> IO(Out):
  do IO<Out>:
    ds : List<&2, Rep.Diag> <- C.check(ck, Proto.path(uri))
    published(~fs, uri, Docs.set_errors(docs, uri, ds))

def hover.of(m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.hover(item)
    case Some{Nav.Here{uri, b}}:
      Proto.hover.local(b)

def definition.of(m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.location(uri, item)
    case Some{Nav.Here{uri, b}}:
      Proto.location.local(uri, b)

def complete.with(~fs: F.Files, +prefix: String, +docs: List<&2, Docs.Doc>, uri: String, +line: U32, +col: U32,
  id: J.Json) -> IO(Out):
  do IO<Out>:
    items : List<&2, Outline.Item> <- Nav.candidates(~fs, docs, uri, prefix, line)
    return Out{reply(id, Proto.completions(items, line, (col - U32.from_nat(String.length(prefix)) : U32), col)),
      False{}, docs}

# the candidates for the name being typed at a position
def complete(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, +line: U32, +col: U32, id: J.Json) -> IO(Out):
  do IO<Out>:
    text : String <- Nav.text_of(~fs, docs, uri)
    complete.with(~fs, Word.before(text, line, col), docs, uri, line, col, id)

def references.of(s: Nav.Sites, uri: String, name: String) -> J.Json:
  Nav.Sites{mine, at} = s
  Proto.locations(uri, name, at)

# only a name bound in the document renames; the editor shows the refusal
def rename.of(s: Nav.Sites, id: J.Json, uri: String, name: String, new: String) -> List<&2, String>:
  Nav.Sites{mine, at} = s
  match mine:
    case True{}:
      reply(id, Proto.rename(uri, name, new, at))
    case False{}:
      [Print.print(Proto.failure(id, "-32803", "only a name bound in this file can be renamed"))]

# every position of the name at a position
def references(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, +line: U32, +col: U32, id: J.Json) -> IO(Out):
  do IO<Out>:
    text : String <- Nav.text_of(~fs, docs, uri)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return Out{reply(id, references.of(s, uri, Word.at(text, line, col))), False{}, docs}

# the edit renaming the name at a position, or a refusal
def renamed(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, +line: U32, +col: U32, id: J.Json, new: String) ->
  IO(Out):
  do IO<Out>:
    text : String <- Nav.text_of(~fs, docs, uri)
    s : Nav.Sites <- Nav.sites(~fs, docs, uri, line, col)
    return Out{rename.of(s, id, uri, Word.at(text, line, col), new), False{}, docs}

# the document's semantic tokens
def semantic(~fs: F.Files, +docs: List<&2, Docs.Doc>, uri: String, id: J.Json) -> IO(Out):
  do IO<Out>:
    text : String <- Nav.text_of(~fs, docs, uri)
    return Out{reply(id, Proto.semantic(Semantic.data(text))), False{}, docs}

def handle.go(~ck: C.Checker, ~fs: F.Files, m: Method, id: J.Json, +params: J.Json, +docs: List<&2, Docs.Doc>) ->
  IO(Out):
  match m:
    case MInitialize{}:
      IO.pure(Out, Out{reply(id, Proto.capabilities()), False{}, docs})
    case MShutdown{}:
      IO.pure(Out, Out{reply(id, J.JNull{}), False{}, docs})
    case MExit{}:
      IO.pure(Out, Out{[], True{}, docs})
    case MOpen{}:
      checked(~fs, uri_of(params), ck,
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.get(params, "textDocument"), "text"), "")))
    case MChange{}:
      published(~fs, uri_of(params),
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.first(J.get(params, "contentChanges")), "text"), "")))
    case MSave{}:
      checked(~fs, uri_of(params), ck, docs)
    case MClose{}:
      IO.pure(Out, Out{[Print.print(Proto.publish(uri_of(params), [], []))], False{}, Docs.del(docs, uri_of(params))})
    case MHover{}:
      do IO<Out>:
        f : Maybe<&2, Nav.Found> <- Nav.hover(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return Out{reply(id, hover.of(f)), False{}, docs}
    case MDefinition{}:
      do IO<Out>:
        f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return Out{reply(id, definition.of(f)), False{}, docs}
    case MSymbols{}:
      do IO<Out>:
        items : List<&2, Outline.Item> <- Nav.outline(~fs, docs, uri_of(params))
        return Out{reply(id, Proto.symbols(items)), False{}, docs}
    case MCompletion{}:
      complete(~fs, docs, uri_of(params), line_of(params), col_of(params), id)
    case MReferences{}:
      references(~fs, docs, uri_of(params), line_of(params), col_of(params), id)
    case MRename{}:
      renamed(~fs, docs, uri_of(params), line_of(params), col_of(params), id, J.str_or(J.get(params, "newName"), ""))
    case MSemantic{}:
      semantic(~fs, docs, uri_of(params), id)
    case MOther{}:
      IO.pure(Out, Out{unknown(id), False{}, docs})

# one message: its method, id and params to handle.go
def handle(~ck: C.Checker, ~fs: F.Files, +msg: J.Json, docs: List<&2, Docs.Doc>) -> IO(Out):
  handle.go(~ck, ~fs, method(J.str_or(J.get(msg, "method"), "")), J.get(msg, "id"), J.get(msg, "params"), docs)

# a parsed message, or null when it did not parse
def decoded(m: Maybe<&2, J.Json>) -> J.Json:
  Maybe.default(&2, J.Json, m, J.JNull{})

# every reply sent, in order
def send_all(~H: Type, ~tr: T.Transport<H>, replies: List<&2, String>, h: H) -> IO(H):
  match replies:
    case Nil{}:
      IO.pure(H, h)
    case Con{body, t}:
      do IO<H>:
        h2 : H <- T.send(H, tr, h, body)
        send_all(~H, ~tr, t, h2)

# the loop goes on with the documents, unless the message said to quit
def next(-H: Type, quit: Bool, h: H, docs: List<&2, Docs.Doc>, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) ->
  IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h, docs)

# the replies sent, then the loop goes on
def answer(~H: Type, ~tr: T.Transport<H>, out: Out, h: H, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  Out{replies, quit, docs} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h)
    next(H, quit, h2, docs, rest)

# one message body handled and answered; none means the peer is gone
def turn(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, ~fs: F.Files, m: Maybe<&2, String>, h: H,
  docs: List<&2, Docs.Doc>, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      do IO<Unit>:
        out : Out <- handle(~ck, ~fs, decoded(Parse.parse(body)), docs)
        answer(~H, ~tr, out, h, rest)

# what recv gave: the handle and maybe a body
def got(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, ~fs: F.Files, r: H & Maybe<&2, String>,
  docs: List<&2, Docs.Doc>, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  (h, m) = r
  turn(~H, ~tr, ~ck, ~fs, m, h, docs, rest)

# serves until exit, the peer's end, or the fuel's (a message each)
def serve(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, ~fs: F.Files, fuel: Nat, h: H,
  docs: List<&2, Docs.Doc>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        r : H & Maybe<&2, String> <- T.recv(H, tr, h)
        got(~H, ~tr, ~ck, ~fs, r, docs, hh => dd => serve(~H, ~tr, ~ck, ~fs, f, hh, dd))
