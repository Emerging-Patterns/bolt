# lsp/proto: the messages the server sends, and the little it reads of a URI.
import Base
import ../json/value.bend as J
import ../json/lex.bend as Lex
import ./frame.bend as Frame
import ./report.bend as Rep
import ../syntax/outline.bend as Outline

def response(id: J.Json, result: J.Json) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("result", result)])

def failure(id: J.Json, code: String, message: String) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id),
    ("error", J.obj([("code", J.JNum{code}), ("message", J.JStr{message})]))])

def notify(method: String, params: J.Json) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("method", J.JStr{method}), ("params", params)])

# what the server can do. It takes whole-text edits (change: 1) for hover,
# definition and symbols; diagnostics still follow open and save, as the
# checker reads files and their imports from disk
def capabilities() -> J.Json:
  J.obj([
    ("capabilities", J.obj([
      ("textDocumentSync", J.obj([("openClose", J.JBool{True{}}), ("change", J.num(1)), ("save", J.JBool{True{}})])),
      ("hoverProvider", J.JBool{True{}}),
      ("definitionProvider", J.JBool{True{}}),
      ("documentSymbolProvider", J.JBool{True{}})])),
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

def line_range(+line: U32) -> J.Json:
  J.obj([("start", position(line, 0)), ("end", position((line + 1 : U32), 0))])

# an item as hover text: its signature as code, then its doc comment
def hover.text(sig: String, +doc: String) -> String:
  "```bend\n" ++ sig ++ "\n```" ++ Bool.pick(String, String.is_empty(doc), "", "\n\n" ++ doc)

def hover(item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  J.obj([("contents", J.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{hover.text(sig, doc)})]))])

def location(uri: String, item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  J.obj([("uri", J.JStr{uri}), ("range", line_range(line))])

# LSP's SymbolKind: module 2, function 12, constant 14, enum member 22, struct 23
def symbol.kind(k: Outline.ItemKind) -> U32:
  match k:
    case Outline.IImport{}:
      2
    case Outline.IDef{}:
      12
    case Outline.ILaw{}:
      14
    case Outline.IType{}:
      23
    case Outline.ICtor{}:
      22

def symbol(item: Outline.Item) -> J.Json:
  Outline.Item{k, name, +line, sig, doc, path} = item
  J.obj([("name", J.JStr{name}), ("kind", J.num(symbol.kind(k))),
    ("range", line_range(line)), ("selectionRange", line_range(line))])

def symbols.go(items: List<&2, Outline.Item>) -> List<&2, J.Json>:
  match items:
    case Nil{}:
      Nil{}
    case Con{item, t}:
      symbol(item) <> symbols.go(t)

def symbols(items: List<&2, Outline.Item>) -> J.Json:
  J.arr(symbols.go(items))

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
