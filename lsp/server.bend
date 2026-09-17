# lsp/server: the loop. Everything outside the process is an injected wire
# service: the transport the messages ride on, and the checker behind the
# diagnostics. Diagnostics run on open and save, against the file on disk.
import Base
import ../json/value.bend as J
import ../json/parse.bend as Parse
import ../json/print.bend as Print
import ./proto.bend as Proto
import ./transport/service.bend as T
import ./checker/service.bend as C
import ./report.bend as Rep

type Method is Data:
  MInitialize{}
  MShutdown{}
  MExit{}
  MCheck{}
  MClose{}
  MOther{}

# what one message leads to: the bodies to send, and whether to stop
type Out is Data:
  Out{replies: List<&2, String>, quit: Bool}

def method(+name: String) -> Method:
  Bool.pick(Method, String.eq(name, "initialize"), MInitialize{},
    Bool.pick(Method, String.eq(name, "shutdown"), MShutdown{},
      Bool.pick(Method, String.eq(name, "exit"), MExit{},
        Bool.pick(Method, String.eq(name, "textDocument/didOpen"), MCheck{},
          Bool.pick(Method, String.eq(name, "textDocument/didSave"), MCheck{},
            Bool.pick(Method, String.eq(name, "textDocument/didClose"), MClose{}, MOther{}))))))

def uri_of(params: J.Json) -> String:
  J.str_or(J.get(J.get(params, "textDocument"), "uri"), "")

# a request the server does not know is refused; a notification is ignored
def unknown(id: J.Json) -> List<&2, String>:
  match id:
    case J.JNull{}:
      []
    case other:
      [Print.print(Proto.failure(other, "-32601", "method not found"))]

def checked(+uri: String, ck: C.Checker) -> IO(Out):
  do IO<Out>:
    ds : List<&2, Rep.Diag> <- C.check(ck, Proto.path(uri))
    return Out{[Print.print(Proto.publish(uri, ds))], False{}}

def handle.go(m: Method, ck: C.Checker, id: J.Json, params: J.Json) -> IO(Out):
  match m:
    case MInitialize{}:
      IO.pure(Out, Out{[Print.print(Proto.response(id, Proto.capabilities()))], False{}})
    case MShutdown{}:
      IO.pure(Out, Out{[Print.print(Proto.response(id, J.JNull{}))], False{}})
    case MExit{}:
      IO.pure(Out, Out{[], True{}})
    case MCheck{}:
      checked(uri_of(params), ck)
    case MClose{}:
      IO.pure(Out, Out{[Print.print(Proto.publish(uri_of(params), []))], False{}})
    case MOther{}:
      IO.pure(Out, Out{unknown(id), False{}})

def handle(ck: C.Checker, +msg: J.Json) -> IO(Out):
  handle.go(method(J.str_or(J.get(msg, "method"), "")), ck, J.get(msg, "id"), J.get(msg, "params"))

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

def next(-H: Type, quit: Bool, h: H, rest: H -> IO(Unit)) -> IO(Unit):
  match quit:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rest(h)

def answer(~H: Type, ~tr: T.Transport<H>, out: Out, h: H, rest: H -> IO(Unit)) -> IO(Unit):
  Out{replies, quit} = out
  do IO<Unit>:
    h2 : H <- send_all(~H, ~tr, replies, h)
    next(H, quit, h2, rest)

def turn(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, m: Maybe<&2, String>, h: H, rest: H -> IO(Unit)) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{body}:
      do IO<Unit>:
        out : Out <- handle(ck, decoded(Parse.parse(body)))
        answer(~H, ~tr, out, h, rest)

def got(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, r: H & Maybe<&2, String>, rest: H -> IO(Unit)) -> IO(Unit):
  (h, m) = r
  turn(~H, ~tr, ~ck, m, h, rest)

# serves until exit, the peer's end, or the fuel's (a message each)
def serve(~H: Type, ~tr: T.Transport<H>, ~ck: C.Checker, fuel: Nat, h: H) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      do IO<Unit>:
        r : H & Maybe<&2, String> <- T.recv(H, tr, h)
        got(~H, ~tr, ~ck, r, hh => serve(~H, ~tr, ~ck, f, hh))
