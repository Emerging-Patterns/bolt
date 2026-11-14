# What each reply of the language server holds, field by field, as LSP 3.17
# names the fields. laws/LspRepliesListEveryEntry.bend says a reply lists one
# entry for each thing; this says what an entry is. An editor reads a reply
# by these names: a field misspelled or left out is a reply the editor
# drops, quietly. The field names, the severities (1 an error, 2 a warning)
# and the markup kind here are the protocol's, written from its spec, not
# read off the code.
#
# - A JSON-RPC reply carries `jsonrpc` 2.0, the request's `id` and a
#   `result`, or an `error` with a `code` and a `message`; a notification
#   carries `jsonrpc`, a `method` and `params`, and no id.
# - A position is a `line` and a `character`; a range a `start` and an
#   `end`. A checker error covers its whole line, up to the start of the
#   next; a finding covers its name, or from its column to the end of the
#   line when it has no length.
# - A diagnostic is a `range`, a `severity`, a `source` and a `message`, and
#   a finding's also its `code`; diagnostics are published for a `uri`,
#   the checker's first, then the linter's.
# - Hover is `contents` in markdown: an item's signature as code, then its
#   doc after a blank line when it has one; a binder's text as code, then
#   what it is in words, and for a local the line it was bound on (from 1).
# - A location is a `uri` and a `range`; a symbol a `name`, a `kind`, a
#   `range` and a `selectionRange`; a completion a `label`, a `kind`, a
#   `detail`, `documentation`, a `filterText` and a `textEdit`; a rename
#   `changes` by uri; semantic tokens their `data`.
# - A file URI's path is the URI without `file://`, its `%XX` read with
#   0-9, a-f and A-F as the hex digits.
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/frame.bend as Frame
import ../src/lsp/report.bend as Rep
import ../src/syntax/outline.bend as Outline
import ../src/syntax/bind.bend as Bind
import ../src/finding.bend as Lint
import ../src/codes.bend as Codes
import ../src/config.bend as Config
import ../src/lsp/enc.bend as Enc
import ../src/lsp/proto.bend as Proto

# a range, as the protocol names its ends
def range(st: J.Json, en: J.Json) -> J.Json:
  Ezjson.obj([("start", st), ("end", en)])

# a markdown text, as hover and documentation carry it
def markdown(text: String) -> J.Json:
  Ezjson.obj([("kind", J.JStr{"markdown"}), ("value", J.JStr{text})])

# the protocol's severity for a level: 1 an error, 2 a warning (grading
# drops an off finding before it is sent)
def severity(l: Config.Level) -> String:
  match l:
    case Config.Error{}:
      "1"
    case Config.Warn{}:
      "2"
    case Config.Off{}:
      "2"

# what a binder is, in the words hover uses
def kind.words(k: Bind.BindKind) -> String:
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

# is a binder a local (bound by a let, a pattern or a `for`)?
def kind.local(k: Bind.BindKind) -> Bool:
  match k:
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      True{}
    case Bind.KFor{}:
      True{}
    case _other:
      False{}

# one of the hex digits a `%XX` may use
type HexDig is Data:
  H0{}
  H1{}
  H2{}
  H3{}
  H4{}
  H5{}
  H6{}
  H7{}
  H8{}
  H9{}
  La{}
  Lb{}
  Lc{}
  Ld{}
  Le{}
  Lf{}
  Ua{}
  Ub{}
  Uc{}
  Ud{}
  Ue{}
  Uf{}

# a hex digit's char
def hex.char(d: HexDig) -> Char:
  match d:
    case H0{}:
      '0'
    case H1{}:
      '1'
    case H2{}:
      '2'
    case H3{}:
      '3'
    case H4{}:
      '4'
    case H5{}:
      '5'
    case H6{}:
      '6'
    case H7{}:
      '7'
    case H8{}:
      '8'
    case H9{}:
      '9'
    case La{}:
      'a'
    case Lb{}:
      'b'
    case Lc{}:
      'c'
    case Ld{}:
      'd'
    case Le{}:
      'e'
    case Lf{}:
      'f'
    case Ua{}:
      'A'
    case Ub{}:
      'B'
    case Uc{}:
      'C'
    case Ud{}:
      'D'
    case Ue{}:
      'E'
    case Uf{}:
      'F'

# a hex digit's value
def hex.value(d: HexDig) -> U32:
  match d:
    case H0{}:
      0
    case H1{}:
      1
    case H2{}:
      2
    case H3{}:
      3
    case H4{}:
      4
    case H5{}:
      5
    case H6{}:
      6
    case H7{}:
      7
    case H8{}:
      8
    case H9{}:
      9
    case La{}:
      10
    case Lb{}:
      11
    case Lc{}:
      12
    case Ld{}:
      13
    case Le{}:
      14
    case Lf{}:
      15
    case Ua{}:
      10
    case Ub{}:
      11
    case Uc{}:
      12
    case Ud{}:
      13
    case Ue{}:
      14
    case Uf{}:
      15

# LAW: a reply to a request carries jsonrpc 2.0, its id and its result
law rpc_response:
  for id: J.Json
  for result: J.Json
  {Proto.response(id, result) == Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("result", result)]) : J.Json}

# LAW: a refusal carries jsonrpc 2.0, the id, and an error with a code and a
# message
law rpc_failure:
  for id: J.Json
  for code: String
  for message: String
  {Proto.failure(id, code, message)
    == Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id),
      ("error", Ezjson.obj([("code", J.JNum{code}), ("message", J.JStr{message})]))]) : J.Json}

# LAW: a notification carries jsonrpc 2.0, a method and params, and no id
law rpc_notify:
  for method: String
  for params: J.Json
  {Proto.notify(method, params)
    == Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("method", J.JStr{method}), ("params", params)]) : J.Json}

# LAW: a position is a line and a character
law position_fields:
  for line: U32
  for character: U32
  {Proto.position.at(line, character)
    == Ezjson.obj([("line", J.JNum{U32.show(line)}), ("character", J.JNum{U32.show(character)})]) : J.Json}

# LAW: a checker error is an error from bend covering its whole line
law diagnostic_fields:
  for +c: Enc.Cols
  for +line: U32
  for msg: String
  {Proto.diagnostic(c, Rep.Diag{line, msg})
    == Ezjson.obj([("range", range(Proto.position(c, line, 0), Proto.position(c, (line + 1 : U32), 0))),
      ("severity", J.JNum{"1"}), ("source", J.JStr{"bend"}), ("message", J.JStr{msg})]) : J.Json}

# LAW: a finding with a length covers that many characters from its column
law finding_range_named:
  for +c: Enc.Cols
  for +line: U32
  for +col: U32
  for +len: U32
  for e: {U32.is_eq(len, 0) == False{} : Bool}
  {Proto.finding_range(c, line, col, len)
    == range(Proto.position(c, line, col), Proto.position(c, line, (col + len : U32))) : J.Json}

# LAW: a finding with no length covers from its column to the end of its line
law finding_range_rest_of_line:
  for +c: Enc.Cols
  for +line: U32
  for +col: U32
  for +len: U32
  for e: {U32.is_eq(len, 0) == True{} : Bool}
  {Proto.finding_range(c, line, col, len)
    == range(Proto.position(c, line, col), Proto.position(c, (line + 1 : U32), 0)) : J.Json}

# LAW: a finding is its range, its level's severity, its code, bolt(group:rule)
# as its source, and its message
law finding_fields:
  for +c: Enc.Cols
  for level: Config.Level
  for path: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +rule: String
  for msg: String
  {Proto.finding(c, Lint.Graded{level, Lint.Finding{path, line, col, len, rule, msg}})
    == Ezjson.obj([("range", Proto.finding_range(c, line, col, len)), ("severity", J.JNum{severity(level)}),
      ("code", J.JStr{Codes.code(rule)}), ("source", J.JStr{Codes.source(rule)}), ("message", J.JStr{msg})])
    : J.Json}

# LAW: diagnostics are published for a document: the checker's, then the
# linter's
law publish_fields:
  for +c: Enc.Cols
  for uri: String
  for ds: List<&2, Rep.Diag>
  for gs: List<&2, Lint.Graded>
  {Proto.publish(c, uri, ds, gs)
    == Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("method", J.JStr{"textDocument/publishDiagnostics"}),
      ("params", Ezjson.obj([("uri", J.JStr{uri}),
        ("diagnostics", Ezjson.arr(List.append(&2, J.Json, Proto.diagnostics(ds, c), Proto.findings(gs, c))))]))])
    : J.Json}

# LAW: a whole line runs from its start to the start of the next
law line_range_whole_line:
  for +c: Enc.Cols
  for +line: U32
  {Proto.line_range(c, line) == range(Proto.position(c, line, 0), Proto.position(c, (line + 1 : U32), 0)) : J.Json}

# LAW: an item's hover is markdown
law hover_fields:
  for k: Outline.ItemKind
  for name: String
  for line: U32
  for sig: String
  for doc: String
  for path: String
  {Proto.hover(Outline.Item{k, name, line, sig, doc, path})
    == Ezjson.obj([("contents", markdown(Proto.hover.text(sig, doc)))]) : J.Json}

# LAW: an item with no doc hovers as its signature, as code
law hover_text_no_doc:
  for sig: String
  for +doc: String
  for e: {String.is_empty(doc) == True{} : Bool}
  {Proto.hover.text(sig, doc) == "```bend\n" ++ sig ++ "\n```" : String}

# LAW: an item with a doc hovers as its signature, as code, then the doc
# after a blank line
law hover_text_doc:
  for sig: String
  for +doc: String
  for e: {String.is_empty(doc) == False{} : Bool}
  {Proto.hover.text(sig, doc) == "```bend\n" ++ sig ++ "\n```" ++ "\n\n" ++ doc : String}

# LAW: an item's location is its whole line
law location_fields:
  for +c: Enc.Cols
  for uri: String
  for k: Outline.ItemKind
  for name: String
  for line: U32
  for sig: String
  for doc: String
  for path: String
  {Proto.location(c, uri, Outline.Item{k, name, line, sig, doc, path})
    == Ezjson.obj([("uri", J.JStr{uri}), ("range", Proto.line_range(c, line))]) : J.Json}

# LAW: a binder hovers as markdown: the text that bound it, as code, then
# what it is
law hover_local_fields:
  for name: String
  for line: U32
  for col: U32
  for +kind: Bind.BindKind
  for note: String
  {Proto.hover.local(Bind.Bind{name, line, col, kind, note})
    == Ezjson.obj([("contents",
      markdown("```bend\n" ++ note ++ "\n```\n\n" ++ Proto.kind_name(kind) ++ Proto.where_bound(kind, line)))])
    : J.Json}

# LAW: each kind of binder is named in its own words
law kind_name_words:
  for k: Bind.BindKind
  {Proto.kind_name(k) == kind.words(k) : String}

# LAW: a local's hover says the line it was bound on, counted from 1; any
# other binder's says nothing more
law where_bound_line:
  for k: Bind.BindKind
  for +line: U32
  {Proto.where_bound(k, line)
    == Bool.pick(String, kind.local(k), ", bound on line " ++ U32.show((line + 1 : U32)), "") : String}

# LAW: a name's range is exactly its characters
law name_range_fields:
  for +c: Enc.Cols
  for +line: U32
  for +col: U32
  for name: String
  {Proto.name_range(c, line, col, name)
    == range(Proto.position(c, line, col), Proto.position(c, line, (col + U32.from_nat(String.length(name)) : U32)))
    : J.Json}

# LAW: a binder's location is exactly its name
law location_local_fields:
  for +c: Enc.Cols
  for uri: String
  for name: String
  for line: U32
  for col: U32
  for kind: Bind.BindKind
  for note: String
  {Proto.location.local(c, uri, Bind.Bind{name, line, col, kind, note})
    == Ezjson.obj([("uri", J.JStr{uri}), ("range", Proto.name_range(c, line, col, name))]) : J.Json}

# LAW: a symbol is a name, a kind, and its whole line as both ranges
law symbol_fields:
  for +c: Enc.Cols
  for k: Outline.ItemKind
  for name: String
  for +line: U32
  for sig: String
  for doc: String
  for path: String
  {Proto.symbol(c, Outline.Item{k, name, line, sig, doc, path})
    == Ezjson.obj([("name", J.JStr{name}), ("kind", J.JNum{U32.show(Proto.symbol.kind(k))}),
      ("range", Proto.line_range(c, line)), ("selectionRange", Proto.line_range(c, line))]) : J.Json}

# LAW: a completion is its name as label, filter text and the text that
# replaces what was typed, its kind, its signature's first line as detail,
# and its doc as markdown
law completion_fields:
  for +c: Enc.Cols
  for k: Outline.ItemKind
  for +name: String
  for l: U32
  for sig: String
  for doc: String
  for path: String
  for +line: U32
  for start: U32
  for col: U32
  {Proto.completion(c, Outline.Item{k, name, l, sig, doc, path}, line, start, col)
    == Ezjson.obj([("label", J.JStr{name}), ("kind", J.JNum{U32.show(Proto.completion.kind(k))}),
      ("detail", J.JStr{Proto.first_line(sig)}), ("documentation", markdown(doc)), ("filterText", J.JStr{name}),
      ("textEdit", Ezjson.obj([("range", range(Proto.position(c, line, start), Proto.position(c, line, col))),
        ("newText", J.JStr{name})]))]) : J.Json}

# LAW: a rename is its edits as the changes of the one document
law rename_fields:
  for c: Enc.Cols
  for uri: String
  for name: String
  for new: String
  for ps: List<&2, Bind.Pos>
  {Proto.rename(c, uri, name, new, ps)
    == Ezjson.obj([("changes", Ezjson.obj([(uri, Ezjson.arr(Proto.edits.go(ps, c, name, new)))]))]) : J.Json}

# LAW: semantic tokens are their data
law semantic_fields:
  for data: List<&2, U32>
  {Proto.semantic(data) == Ezjson.obj([("data", Ezjson.arr(Proto.nums(data)))]) : J.Json}

# LAW: each hex digit of a `%XX` has its value: 0-9, then a-f and A-F as
# 10-15
law hex_digit_values:
  for d: HexDig
  {Proto.hex(hex.char(d)) == hex.value(d) : U32}

# LAW: a file URI's path is the URI without `file://`, decoded
law path_drops_scheme:
  for rest: String
  {Proto.path("file://" ++ rest) == Frame.decode(Proto.unpercent(String.to_list(rest))) : String}

# LAW: any other URI is decoded whole
law path_keeps_other:
  for +uri: String
  for e: {String.starts_with(uri, "file://") == False{} : Bool}
  {Proto.path(uri) == Frame.decode(Proto.unpercent(String.to_list(uri))) : String}

# the source of a rule's row, none for no row. Law vocabulary: bolt never
# calls it
def source.named(m: Maybe<&2, Codes.Entry>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Codes.Entry{s, _id, grp}}:
      Some{"bolt(" ++ grp ++ ":" ++ s ++ ")"}

# LAW: a rule's finding is shown in the editor under the source
# `bolt(group:slug)`
law source_names_group_and_rule:
  for +s: String
  for id: String
  for +grp: String
  {Codes.source.at(Some{Codes.Entry{s, id, grp}}) == "bolt(" ++ grp ++ ":" ++ s ++ ")" : String}

# LAW: and a finding of no rule under `bolt`
law source_of_no_rule:
  for m: Maybe<&2, Codes.Entry>
  {Codes.source.at(m) == Maybe.default(&2, String, source.named(m), "bolt") : String}
