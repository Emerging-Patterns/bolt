# lsp/proto: the messages the server sends, and the little it reads of a URI.
import Base
import 0xd9c8d4d2899ddda845dfa7525a3568ea/main.bend as Ezjson
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J
import ./frame.bend as Frame
import ./report.bend as Rep
import ../syntax/outline.bend as Outline
import ../syntax/bind.bend as Bind
import ./semantic.bend as Semantic
import ../finding.bend as Lint
import ../codes.bend as Codes
import ../config.bend as Config
import ../version.bend as Ver
import ./enc.bend as Enc

# strings as JSON strings
def strings(ss: List<&2, String>) -> List<&2, J.Json>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      J.JStr{h} <> strings(t)

# a reply to a request
def response(id: J.Json, result: J.Json) -> J.Json:
  Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("result", result)])

# a refusal of a request, with LSP's error code and a message
def failure(id: J.Json, code: String, message: String) -> J.Json:
  Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id),
    ("error", Ezjson.obj([("code", J.JNum{code}), ("message", J.JStr{message})]))])

# a notification: no id, no reply expected
def notify(method: String, params: J.Json) -> J.Json:
  Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("method", J.JStr{method}), ("params", params)])

# what the server can do. It takes whole-text edits (change: 1) for hover,
# definition and symbols; diagnostics still follow open and save, as the
# checker reads files and their imports from disk
def capabilities(ee: Enc.Enc) -> J.Json:
  Ezjson.obj([
    ("capabilities", Ezjson.obj([
      ("positionEncoding", J.JStr{Enc.name(ee)}),
      ("textDocumentSync", Ezjson.obj([("openClose", J.JBool{True{}}), ("change", J.JNum{U32.show(1)}), ("save", J.JBool{True{}})])),
      ("hoverProvider", J.JBool{True{}}),
      ("definitionProvider", J.JBool{True{}}),
      ("documentSymbolProvider", J.JBool{True{}}),
      ("completionProvider", Ezjson.obj([("triggerCharacters", Ezjson.arr([J.JStr{"."}]))])),
      ("referencesProvider", J.JBool{True{}}),
      ("renameProvider", J.JBool{True{}}),
      ("semanticTokensProvider", Ezjson.obj([
        ("legend", Ezjson.obj([("tokenTypes", Ezjson.arr(strings(Semantic.legend()))), ("tokenModifiers", Ezjson.arr([]))])),
        ("full", J.JBool{True{}})]))])),
    ("serverInfo", Ezjson.obj([("name", J.JStr{"bolt"}), ("version", J.JStr{Ver.text()})]))])

# an LSP position as sent: a line and a character already in the negotiated
# encoding
def position.at(line: U32, character: U32) -> J.Json:
  Ezjson.obj([("line", J.JNum{U32.show(line)}), ("character", J.JNum{U32.show(character)})])

# an LSP position (0-based line and a code-point character), its character
# sent in the document's negotiated encoding
def position(cc: Enc.Cols, +line: U32, character: U32) -> J.Json:
  position.at(line, Enc.out(cc, line, character))

# the checker gives a line and no columns: a diagnostic covers its whole line
def diagnostic(+cc: Enc.Cols, dd: Rep.Diag) -> J.Json:
  Rep.Diag{+line, msg} = dd
  Ezjson.obj([
    ("range", Ezjson.obj([("start", position(cc, line, 0)), ("end", position(cc, (line + 1 : U32), 0))])),
    ("severity", J.JNum{U32.show(1)}), ("source", J.JStr{"bend"}), ("message", J.JStr{msg})])

# diagnostics as JSON
def diagnostics(ds: List<&2, Rep.Diag>, +cc: Enc.Cols) -> List<&2, J.Json>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      diagnostic(cc, d) <> diagnostics(t, cc)

# a finding's range: its name, or from its column to the end of the line
def finding_range(+cc: Enc.Cols, +line: U32, +col: U32, +len: U32) -> J.Json:
  Ezjson.obj([("start", position(cc, line, col)),
    ("end", Bool.pick(J.Json, U32.is_eq(len, 0), position(cc, (line + 1 : U32), 0),
      position(cc, line, (col + len : U32))))])

# a graded lint finding as a diagnostic: an error or a warning by its level,
# its stable code, and bolt(group:slug) as the source
def finding(cc: Enc.Cols, gg: Lint.Graded) -> J.Json:
  Lint.Graded{level, Lint.Finding{path, line, col, len, +rule, msg}} = gg
  Ezjson.obj([("range", finding_range(cc, line, col, len)),
    ("severity", J.JNum{U32.show(Bool.pick(U32, Config.is_error(level), 1, 2))}),
    ("code", J.JStr{Codes.code(rule)}), ("source", J.JStr{Codes.source(rule)}), ("message", J.JStr{msg})])

# findings as JSON
def findings(gs: List<&2, Lint.Graded>, +cc: Enc.Cols) -> List<&2, J.Json>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      finding(cc, g) <> findings(t, cc)

# the publishDiagnostics notification for a document: the checker's errors,
# then the linter's findings
def publish(+cc: Enc.Cols, uri: String, ds: List<&2, Rep.Diag>, gs: List<&2, Lint.Graded>) -> J.Json:
  notify("textDocument/publishDiagnostics",
    Ezjson.obj([("uri", J.JStr{uri}), ("diagnostics", Ezjson.arr(List.append(&2, J.Json, diagnostics(ds, cc), findings(gs, cc))))]))

# a whole line as a range
def line_range(+cc: Enc.Cols, +line: U32) -> J.Json:
  Ezjson.obj([("start", position(cc, line, 0)), ("end", position(cc, (line + 1 : U32), 0))])

# an item as hover text: its signature as code, then its doc comment
def hover.text(sig: String, +doc: String) -> String:
  "```bend\n" ++ sig ++ "\n```" ++ Bool.pick(String, String.is_empty(doc), "", "\n\n" ++ doc)

# an item as hover: signature, then doc
def hover(item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  Ezjson.obj([("contents", Ezjson.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{hover.text(sig, doc)})]))])

# an item's location: its whole line
def location(cc: Enc.Cols, uri: String, item: Outline.Item) -> J.Json:
  Outline.Item{k, name, line, sig, doc, path} = item
  Ezjson.obj([("uri", J.JStr{uri}), ("range", line_range(cc, line))])

# what a binder is, in words
def kind_name(kk: Bind.BindKind) -> String:
  match kk:
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
def where_bound(kk: Bind.BindKind, line: U32) -> String:
  match kk:
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
def hover.local(bb: Bind.Bind) -> J.Json:
  Bind.Bind{name, line, col, +kind, note} = bb
  Ezjson.obj([("contents", Ezjson.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{"```bend\n" ++ note ++ "\n```\n\n" ++
    kind_name(kind) ++ where_bound(kind, line)})]))])

# exactly a name's range
def name_range(+cc: Enc.Cols, +line: U32, +col: U32, name: String) -> J.Json:
  Ezjson.obj([("start", position(cc, line, col)),
    ("end", position(cc, line, (col + U32.from_nat(String.length(name)) : U32)))])

# exactly the binder's name
def location.local(cc: Enc.Cols, uri: String, bb: Bind.Bind) -> J.Json:
  Bind.Bind{name, line, col, kind, note} = bb
  Ezjson.obj([("uri", J.JStr{uri}), ("range", name_range(cc, line, col, name))])

# LSP's SymbolKind: module 2, function 12, constant 14, enum member 22, struct 23
def symbol.kind(kk: Outline.ItemKind) -> U32:
  match kk:
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
def symbol(+cc: Enc.Cols, item: Outline.Item) -> J.Json:
  Outline.Item{k, name, +line, sig, doc, path} = item
  Ezjson.obj([("name", J.JStr{name}), ("kind", J.JNum{U32.show(symbol.kind(k))}),
    ("range", line_range(cc, line)), ("selectionRange", line_range(cc, line))])

def symbols.go(items: List<&2, Outline.Item>, +cc: Enc.Cols) -> List<&2, J.Json>:
  match items:
    case Nil{}:
      Nil{}
    case Con{item, t}:
      symbol(cc, item) <> symbols.go(t, cc)

# the document symbols
def symbols(cc: Enc.Cols, items: List<&2, Outline.Item>) -> J.Json:
  Ezjson.arr(symbols.go(items, cc))

# LSP's CompletionItemKind: function 3, module 9, enum member 20, constant 21,
# struct 22
def completion.kind(kk: Outline.ItemKind) -> U32:
  match kk:
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
def first_line(s2: String) -> String:
  Maybe.default(&2, String, List.head(&2, String, String.lines(s2)), "")

# a candidate replaces everything typed of the name, dots included: the
# editor's own idea of a word stops at a dot
def completion(+cc: Enc.Cols, item: Outline.Item, +line: U32, start: U32, col: U32) -> J.Json:
  Outline.Item{k, +name, l, sig, doc, path} = item
  Ezjson.obj([("label", J.JStr{name}), ("kind", J.JNum{U32.show(completion.kind(k))}), ("detail", J.JStr{first_line(sig)}),
    ("documentation", Ezjson.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{doc})])),
    ("filterText", J.JStr{name}),
    ("textEdit", Ezjson.obj([("range", Ezjson.obj([("start", position(cc, line, start)), ("end", position(cc, line, col))])),
      ("newText", J.JStr{name})]))])

def completions.go(
  items: List<&2, Outline.Item>,
  +cc: Enc.Cols,
  +line: U32,
  +start: U32,
  +col: U32
) -> List<&2, J.Json>:
  match items:
    case Nil{}:
      Nil{}
    case Con{item, t}:
      completion(cc, item, line, start, col) <> completions.go(t, cc, line, start, col)

# isIncomplete: the server filtered by the prefix, so the editor asks again
# as the prefix grows
def completions(cc: Enc.Cols, items: List<&2, Outline.Item>, line: U32, start: U32, col: U32) -> J.Json:
  Ezjson.obj([("isIncomplete", J.JBool{True{}}), ("items", Ezjson.arr(completions.go(items, cc, line, start, col)))])

# a hex digit's value: 0-9, then a-f and A-F as 10-15
def hex(ch: Char) -> U32:
  +x = Char.to_u32(ch)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32),
    Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

# a file URI's path: the scheme dropped, the %XX bytes decoded as UTF-8
def unpercent(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{'%', Con{a, Con{b, t}}}:
      +hi = hex(a)
      +lo = hex(b)
      (hi * 16 + lo : U32) <> unpercent(t)
    case Con{c, t}:
      Frame.encode.one(Char.to_u32(c), unpercent(t))

# a file URI's path: the scheme dropped, the %XX bytes decoded as UTF-8
def path(+uri: String) -> String:
  Frame.decode(unpercent(String.to_list(
    Bool.pick(String, String.starts_with(uri, "file://"), String.drop(uri, 7n), uri))))

# references and rename
# ---------------------

def locations.go(ps: List<&2, Bind.Pos>, +cc: Enc.Cols, +uri: String, +name: String) -> List<&2, J.Json>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Bind.Pos{l, c}, rest}:
      Ezjson.obj([("uri", J.JStr{uri}), ("range", name_range(cc, l, c, name))]) <> locations.go(rest, cc, uri, name)

# the positions a name is at, as Locations
def locations(cc: Enc.Cols, uri: String, name: String, ps: List<&2, Bind.Pos>) -> J.Json:
  Ezjson.arr(locations.go(ps, cc, uri, name))

def edits.go(ps: List<&2, Bind.Pos>, +cc: Enc.Cols, +name: String, +new: String) -> List<&2, J.Json>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Bind.Pos{l, c}, rest}:
      Ezjson.obj([("range", name_range(cc, l, c, name)), ("newText", J.JStr{new})]) <> edits.go(rest, cc, name, new)

# a WorkspaceEdit over the one document
def rename(cc: Enc.Cols, uri: String, name: String, new: String, ps: List<&2, Bind.Pos>) -> J.Json:
  Ezjson.obj([("changes", Ezjson.obj([(uri, Ezjson.arr(edits.go(ps, cc, name, new)))]))])

# numbers as JSON numbers
def nums(ns: List<&2, U32>) -> List<&2, J.Json>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      J.JNum{U32.show(h)} <> nums(t)

# the semantic tokens response
def semantic(data: List<&2, U32>) -> J.Json:
  Ezjson.obj([("data", Ezjson.arr(nums(data)))])
