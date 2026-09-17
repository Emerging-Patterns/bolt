# lsp/server: the loop. Everything outside the process is an injected wire
# service: the transport the messages ride on, the checker behind the
# diagnostics, the files behind imports and Base. The open documents are the
# loop's state. Diagnostics run on open and save, against the file on disk.
import Base
import ../json/value.bend as J
import ../json/parse.bend as Parse
import ../json/print.bend as Print
import ./proto.bend as Proto
import ./docs.bend as Docs
import ./nav.bend as Nav
import ./transport/service.bend as T
import ./checker/service.bend as C
import ./files/service.bend as F
import ./report.bend as Rep
import ../syntax/outline.bend as Outline

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
  MOther{}

# what one message leads to: the bodies to send, whether to stop, the documents
type Out is Data:
  Out{replies: List<&2, String>, quit: Bool, docs: List<&2, Docs.Doc>}

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
                    Bool.pick(Method, String.eq(name, "textDocument/documentSymbol"), MSymbols{}, MOther{}))))))))))

def uri_of(params: J.Json) -> String:
  J.str_or(J.get(J.get(params, "textDocument"), "uri"), "")

def line_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "line"), 0)

def col_of(params: J.Json) -> U32:
  J.u32_or(J.get(J.get(params, "position"), "character"), 0)

def reply(id: J.Json, result: J.Json) -> List<&2, String>:
  [Print.print(Proto.response(id, result))]

# a request the server does not know is refused; a notification is ignored
def unknown(id: J.Json) -> List<&2, String>:
  match id:
    case J.JNull{}:
      []
    case other:
      [Print.print(Proto.failure(other, "-32601", "method not found"))]

def checked(+uri: String, ck: C.Checker, docs: List<&2, Docs.Doc>) -> IO(Out):
  do IO<Out>:
    ds : List<&2, Rep.Diag> <- C.check(ck, Proto.path(uri))
    return Out{[Print.print(Proto.publish(uri, ds))], False{}, docs}

def hover.of(m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.hover(item)

def definition.of(m: Maybe<&2, Nav.Found>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{Nav.Found{uri, item}}:
      Proto.location(uri, item)

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
      checked(uri_of(params), ck,
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.get(params, "textDocument"), "text"), "")))
    case MChange{}:
      IO.pure(Out, Out{[], False{},
        Docs.set(docs, uri_of(params), J.str_or(J.get(J.first(J.get(params, "contentChanges")), "text"), ""))})
    case MSave{}:
      checked(uri_of(params), ck, docs)
    case MClose{}:
      IO.pure(Out, Out{[Print.print(Proto.publish(uri_of(params), []))], False{}, Docs.del(docs, uri_of(params))})
    case MHover{}:
      do IO<Out>:
        f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return Out{reply(id, hover.of(f)), False{}, docs}
    case MDefinition{}:
      do IO<Out>:
        f : Maybe<&2, Nav.Found> <- Nav.at(~fs, docs, uri_of(params), line_of(params), col_of(params))
        return Out{reply(id, definition.of(f)), False{}, docs}
    case MSymbols{}:
      do IO<Out>:
        items : List<&2, Outline.Item> <- Nav.outline(~fs, docs, uri_of(params))
        return Out{reply(id, Proto.symbols(items)), False{}, docs}
    case MOther{}:
      IO.pure(Out, Out{unknown(id), False{}, docs})

def handle(~ck: C.Checker, ~fs: F.Files, +msg: J.Json, docs: List<&2, Docs.Doc>) -> IO(Out):
  handle.go(~ck, ~fs, method(J.str_or(J.get(msg, "method"), "")), J.get(msg, "id"), J.get(msg, "params"), docs)

def decoded(m: Maybe<&2, J.Json>) -> J.Json:
  Maybe.default(&2, J.Json, m, J.JNull{})

def send_all(~H: Type, ~tr: T.Transport<H>, replies: List<&2, String>, h: H) -> IO(H):
  match replies:
    case Nil{}:
      IO.pure(H, h)
    case Con{body, t}:
      do IO<H>:
        h2 : H <- T.send(H, tr, h, body)
        send_all(~H, ~tr, t, h2)

def next(-H: Type, quit: Bool, h: H, docs: List<&2, Docs.Doc>, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) ->
  IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h, docs)

def answer(~H: Type, ~tr: T.Transport<H>, out: Out, h: H, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  Out{replies, quit, docs} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h)
    next(H, quit, h2, docs, rest)

def turn(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, ~fs: F.Files, m: Maybe<&2, String>, h: H,
  docs: List<&2, Docs.Doc>, rest: H -> List<&2, Docs.Doc> -> IO(Unit)) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      do IO<Unit>:
        out : Out <- handle(~ck, ~fs, decoded(Parse.parse(body)), docs)
        answer(~H, ~tr, out, h, rest)

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
