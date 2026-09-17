# lsp/proto: the messages the server sends, and the little it reads of a URI.
import Base
import ../json/value.bend as J
import ../json/lex.bend as Lex
import ./frame.bend as Frame
import ./report.bend as Rep

def response(id: J.Json, result: J.Json) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("result", result)])

def failure(id: J.Json, code: String, message: String) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id),
    ("error", J.obj([("code", J.JNum{code}), ("message", J.JStr{message})]))])

def notify(method: String, params: J.Json) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("method", J.JStr{method}), ("params", params)])

# what the server can do: it wants open, save and close, and no edits (the
# checker reads files and their imports from disk)
def capabilities() -> J.Json:
  J.obj([
    ("capabilities", J.obj([("textDocumentSync",
      J.obj([("openClose", J.JBool{True{}}), ("change", J.num(0)), ("save", J.JBool{True{}})]))])),
    ("serverInfo", J.obj([("name", J.JStr{"bend-lsp"})]))])

def position(line: U32, character: U32) -> J.Json:
  J.obj([("line", J.num(line)), ("character", J.num(character))])

# the checker gives a line and no columns: a diagnostic covers its whole line
def diagnostic(d: Rep.Diag) -> J.Json:
  Rep.Diag{+line, msg} = d
  J.obj([
    ("range", J.obj([("start", position(line, 0)), ("end", position((line + 1 : U32), 0))])),
    ("severity", J.num(1)), ("source", J.JStr{"bend"}), ("message", J.JStr{msg})])

def diagnostics(ds: List<&2, Rep.Diag>) -> List<&2, J.Json>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      diagnostic(d) <> diagnostics(t)

def publish(uri: String, ds: List<&2, Rep.Diag>) -> J.Json:
  notify("textDocument/publishDiagnostics",
    J.obj([("uri", J.JStr{uri}), ("diagnostics", J.arr(diagnostics(ds)))]))

# a file URI's path: the scheme dropped, the %XX bytes decoded as UTF-8
def unpercent(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{'%', Con{a, Con{b, t}}}:
      (Lex.hex(a) * 16 + Lex.hex(b) : U32) <> unpercent(t)
    case Con{c, t}:
      Frame.encode.one(Char.to_u32(c), unpercent(t))

def path(+uri: String) -> String:
  Frame.decode(unpercent(String.to_list(
    Bool.pick(String, String.starts_with(uri, "file://"), String.drop(uri, 7n), uri))))
