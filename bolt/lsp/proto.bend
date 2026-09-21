# lsp/proto: the messages the server sends, and the little it reads of a URI.
import Base
import 0xa3c2445eb44c5d8406e6229be518fccb/value.bend as J
import 0xa3c2445eb44c5d8406e6229be518fccb/lex.bend as Lex
import ./frame.bend as Frame
import ./report.bend as Rep
import ../../syntax/outline.bend as Outline
import ../../syntax/bind.bend as Bind
import ./semantic.bend as Semantic
import ../finding.bend as Lint
import ../config.bend as Config
import ../version.bend as Ver

# strings as JSON strings
def strings(ss: List<&2, String>) -> List<&2, J.Json>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      J.JStr{h} <> strings(t)

# a reply to a request
def response(id: J.Json, result: J.Json) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("result", result)])

# a refusal of a request, with LSP's error code and a message
def failure(id: J.Json, code: String, message: String) -> J.Json:
  J.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id),
    ("error", J.obj([("code", J.JNum{code}), ("message", J.JStr{message})]))])

# a notification: no id, no reply expected
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
      ("documentSymbolProvider", J.JBool{True{}}),
      ("completionProvider", J.obj([("triggerCharacters", J.arr([J.JStr{"."}]))])),
      ("referencesProvider", J.JBool{True{}}),
      ("renameProvider", J.JBool{True{}}),
      ("semanticTokensProvider", J.obj([
        ("legend", J.obj([("tokenTypes", J.arr(strings(Semantic.legend()))), ("tokenModifiers", J.arr([]))])),
        ("full", J.JBool{True{}})]))])),
    ("serverInfo", J.obj([("name", J.JStr{"bolt"}), ("version", J.JStr{Ver.text()})]))])

# an LSP position (0-based line and character)
def position(line: U32, character: U32) -> J.Json:
  J.obj([("line", J.num(line)), ("character", J.num(character))])

# the checker gives a line and no columns: a diagnostic covers its whole line
def diagnostic(d: Rep.Diag) -> J.Json:
  Rep.Diag{+line, msg} = d
  J.obj([
    ("range", J.obj([("start", position(line, 0)), ("end", position((line + 1 : U32), 0))])),
    ("severity", J.num(1)), ("source", J.JStr{"bend"}), ("message", J.JStr{msg})])

# diagnostics as JSON
def diagnostics(ds: List<&2, Rep.Diag>) -> List<&2, J.Json>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      diagnostic(d) <> diagnostics(t)

# a finding's range: its name, or from its column to the end of the line
def finding_range(+line: U32, +col: U32, +len: U32) -> J.Json:
  J.obj([("start", position(line, col)),
    ("end", Bool.pick(J.Json, U32.is_eq(len, 0), position((line + 1 : U32), 0), position(line, (col + len : U32))))])

# a graded lint finding as a diagnostic: an error or a warning by its level,
# its rule as the code
def finding(g: Lint.Graded) -> J.Json:
  Lint.Graded{level, Lint.Finding{path, line, col, len, rule, msg}} = g
  J.obj([("range", finding_range(line, col, len)), ("severity", J.num(Bool.pick(U32, Config.is_error(level), 1, 2))),
    ("code", J.JStr{rule}), ("source", J.JStr{"bolt"}), ("message", J.JStr{msg})])

# findings as JSON
def findings(gs: List<&2, Lint.Graded>) -> List<&2, J.Json>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      finding(g) <> findings(t)

# the publishDiagnostics notification for a document: the checker's errors,
# then the linter's findings
def publish(uri: String, ds: List<&2, Rep.Diag>, gs: List<&2, Lint.Graded>) -> J.Json:
  notify("textDocument/publishDiagnostics",
    J.obj([("uri", J.JStr{uri}), ("diagnostics", J.arr(List.append(&2, J.Json, diagnostics(ds), findings(gs))))]))

# a whole line as a range
def line_range(+line: U32) -> J.Json:
  J.obj([("start", position(line, 0)), ("end", position((line + 1 : U32), 0))])

# an item as hover text: its signature as code, then its doc comment
def hover.text(sig: String, +doc: String) -> String:
  "```bend\n" ++ sig ++ "\n```" ++ Bool.pick(String, String.is_empty(doc), "", "\n\n" ++ doc)

# an item as hover: signature, then doc
def hover(item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  J.obj([("contents", J.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{hover.text(sig, doc)})]))])

# an item's location: its whole line
def location(uri: String, item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  J.obj([("uri", J.JStr{uri}), ("range", line_range(line))])

# what a binder is, in words
def kind_name(k: Bind.BindKind) -> String:
  match k:
    case Bind.KItem{}:
      "item"
    case Bind.KCtor{}:
      "constructor"
    case Bind.KParam{}:
      "parameter"
    case Bind.KTypeParam{}:
      "type parameter"
    case Bind.KField{}:
      "field"
    case Bind.KLocal{}:
      "local"
    case Bind.KPat{}:
      "local"
    case Bind.KFor{}:
      "local"
    case Bind.KTypeVar{}:
      "type variable"

# where a local was bound, for hover
def where_bound(k: Bind.BindKind, line: U32) -> String:
  match k:
    case Bind.KLocal{}:
      ", bound on line " ++ U32.show((line + 1 : U32))
    case Bind.KPat{}:
      ", bound on line " ++ U32.show((line + 1 : U32))
    case Bind.KFor{}:
      ", bound on line " ++ U32.show((line + 1 : U32))
    case other:
      ""

# a binder of the document: the text that bound it, and what it is. The
# server knows binding sites, not types: only a declaration carries one
def hover.local(b: Bind.Bind) -> J.Json:
  Bind.Bind{name, line, col, +kind, note} = b
  J.obj([("contents", J.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{"```bend\n" ++ note ++ "\n```\n\n" ++
    kind_name(kind) ++ where_bound(kind, line)})]))])

# exactly a name's range
def name_range(+line: U32, +col: U32, name: String) -> J.Json:
  J.obj([("start", position(line, col)), ("end", position(line, (col + U32.from_nat(String.length(name)) : U32)))])

# exactly the binder's name
def location.local(uri: String, b: Bind.Bind) -> J.Json:
  Bind.Bind{name, line, col, kind, note} = b
  J.obj([("uri", J.JStr{uri}), ("range", name_range(line, col, name))])

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
    case Outline.ILocal{}:
      13

# an item as a DocumentSymbol
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

# the document symbols
def symbols(items: List<&2, Outline.Item>) -> J.Json:
  J.arr(symbols.go(items))

# LSP's CompletionItemKind: function 3, module 9, enum member 20, constant 21,
# struct 22
def completion.kind(k: Outline.ItemKind) -> U32:
  match k:
    case Outline.IImport{}:
      9
    case Outline.IDef{}:
      3
    case Outline.ILaw{}:
      21
    case Outline.IType{}:
      22
    case Outline.ICtor{}:
      20
    case Outline.ILocal{}:
      6

# a text's first line
def first_line(s: String) -> String:
  Maybe.default(&2, String, List.head(&2, String, String.lines(s)), "")

# a candidate replaces everything typed of the name, dots included: the
# editor's own idea of a word stops at a dot
def completion(item: Outline.Item, +line: U32, start: U32, col: U32) -> J.Json:
  Outline.Item{k, +name, l, sig, doc, path} = item
  J.obj([("label", J.JStr{name}), ("kind", J.num(completion.kind(k))), ("detail", J.JStr{first_line(sig)}),
    ("documentation", J.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{doc})])),
    ("filterText", J.JStr{name}),
    ("textEdit", J.obj([("range", J.obj([("start", position(line, start)), ("end", position(line, col))])),
      ("newText", J.JStr{name})]))])

def completions.go(items: List<&2, Outline.Item>, +line: U32, +start: U32, +col: U32) -> List<&2, J.Json>:
  match items:
    case Nil{}:
      Nil{}
    case Con{item, t}:
      completion(item, line, start, col) <> completions.go(t, line, start, col)

# isIncomplete: the server filtered by the prefix, so the editor asks again
# as the prefix grows
def completions(items: List<&2, Outline.Item>, line: U32, start: U32, col: U32) -> J.Json:
  J.obj([("isIncomplete", J.JBool{True{}}), ("items", J.arr(completions.go(items, line, start, col)))])

# a file URI's path: the scheme dropped, the %XX bytes decoded as UTF-8
def unpercent(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{'%', Con{a, Con{b, t}}}:
      +hi = Lex.hex(a)
      +lo = Lex.hex(b)
      (hi * 16 + lo : U32) <> unpercent(t)
    case Con{c, t}:
      Frame.encode.one(Char.to_u32(c), unpercent(t))

# a file URI's path: the scheme dropped, the %XX bytes decoded as UTF-8
def path(+uri: String) -> String:
  Frame.decode(unpercent(String.to_list(
    Bool.pick(String, String.starts_with(uri, "file://"), String.drop(uri, 7n), uri))))

# references and rename
# ---------------------

def locations.go(ps: List<&2, Bind.Pos>, +uri: String, +name: String) -> List<&2, J.Json>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Bind.Pos{l, c}, rest}:
      J.obj([("uri", J.JStr{uri}), ("range", name_range(l, c, name))]) <> locations.go(rest, uri, name)

# the positions a name is at, as Locations
def locations(uri: String, name: String, ps: List<&2, Bind.Pos>) -> J.Json:
  J.arr(locations.go(ps, uri, name))

def edits.go(ps: List<&2, Bind.Pos>, +name: String, +new: String) -> List<&2, J.Json>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Bind.Pos{l, c}, rest}:
      J.obj([("range", name_range(l, c, name)), ("newText", J.JStr{new})]) <> edits.go(rest, name, new)

# a WorkspaceEdit over the one document
def rename(uri: String, name: String, new: String, ps: List<&2, Bind.Pos>) -> J.Json:
  J.obj([("changes", J.obj([(uri, J.arr(edits.go(ps, name, new)))]))])

# numbers as JSON numbers
def nums(ns: List<&2, U32>) -> List<&2, J.Json>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      J.num(h) <> nums(t)

# the semantic tokens response
def semantic(data: List<&2, U32>) -> J.Json:
  J.obj([("data", J.arr(nums(data)))])
