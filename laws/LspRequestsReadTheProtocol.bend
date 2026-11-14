# How the language server reads what an editor sends, by the names LSP 3.17
# gives them. laws/LspRepliesFollowTheProtocol.bend says what the server
# writes; this says what it reads. A method or field read under the wrong
# name is a request the server answers as unknown, or answers about the
# wrong place, without a word.
#
# - Each method the server handles is read by its name in the spec, and any
#   other name (none at all included) as a method it does not know.
# - A message's method is its `method`, its id its `id`; the document a
#   request is about is `textDocument.uri`, and its position
#   `position.line` and `position.character`.
# - A document's text on open is `textDocument.text`, and on change the
#   `text` of the first of `contentChanges` (the whole document: the server
#   asks for full sync).
# - The position encodings are named `utf-16` and `utf-32`.
# - The semantic token legend uses the spec's own token type names, in the
#   order the server numbers them.
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/enc.bend as Enc
import ../src/lsp/semantic.bend as Semantic
import ../src/lsp/server.bend as Server
import ../src/lsp/nav.bend as Nav
import ../src/syntax/bind.bend as Bind

# a method's name in the spec; none for a method the server does not know
def method.wire(mm: Server.Method) -> String:
  match mm:
    case Server.MInitialize{}:
      "initialize"
    case Server.MShutdown{}:
      "shutdown"
    case Server.MExit{}:
      "exit"
    case Server.MOpen{}:
      "textDocument/didOpen"
    case Server.MChange{}:
      "textDocument/didChange"
    case Server.MSave{}:
      "textDocument/didSave"
    case Server.MClose{}:
      "textDocument/didClose"
    case Server.MHover{}:
      "textDocument/hover"
    case Server.MDefinition{}:
      "textDocument/definition"
    case Server.MSymbols{}:
      "textDocument/documentSymbol"
    case Server.MCompletion{}:
      "textDocument/completion"
    case Server.MReferences{}:
      "textDocument/references"
    case Server.MRename{}:
      "textDocument/rename"
    case Server.MSemantic{}:
      "textDocument/semanticTokens/full"
    case Server.MOther{}:
      ""

# an encoding's name in the spec
def enc.wire(ee: Enc.Enc) -> String:
  match ee:
    case Enc.Utf16{}:
      "utf-16"
    case Enc.Utf32{}:
      "utf-32"

# the spec's token type names the legend lists, in the server's order
def legend.wire() -> List<&2, String>:
  ["keyword", "function", "type", "enumMember", "parameter", "variable", "property", "string", "number",
   "comment", "typeParameter"]

# LAW: each method is read by its name in the spec, and no name as none
law method_by_wire_name:
  for mm: Server.Method
  {Server.method(method.wire(mm)) == mm : Server.Method}

# LAW: a message's method is its `method`
law request_method_field:
  for +name: String
  for id: J.Json
  for params: J.Json
  {Server.name_of(Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("method", J.JStr{name}), ("params", params)]))
    == name : String}

# LAW: a message's id is its `id`
law request_id_field:
  for +name: String
  for id: J.Json
  for params: J.Json
  {Server.id_of(Ezjson.obj([("jsonrpc", J.JStr{"2.0"}), ("id", id), ("method", J.JStr{name}), ("params", params)]))
    == id : J.Json}

# LAW: a request is about the document at `textDocument.uri`
law request_uri_field:
  for uri: String
  for pos: J.Json
  {Server.uri_of(Ezjson.obj([("textDocument", Ezjson.obj([("uri", J.JStr{uri})])), ("position", pos)])) == uri
    : String}

# LAW: an opened document's text is `textDocument.text`
law opened_text_field:
  for uri: String
  for text: String
  {Server.opened_text(Ezjson.obj([("textDocument", Ezjson.obj([("uri", J.JStr{uri}), ("text", J.JStr{text})]))]))
    == text : String}

# LAW: a changed document's text is the `text` of the first of
# `contentChanges`, whatever changes follow it
law changed_text_field:
  for doc: J.Json
  for text: String
  for more: J.Json
  {Server.changed_text(Ezjson.obj([("textDocument", doc),
      ("contentChanges", J.JArr{J.JCons{Ezjson.obj([("text", J.JStr{text})]), more}})])) == text : String}

# LAW: a request's line is `position.line`
law request_line_field:
  for doc: J.Json
  for line: String
  for character: String
  {Server.line_of(Ezjson.obj([("textDocument", doc),
    ("position", Ezjson.obj([("line", J.JNum{line}), ("character", J.JNum{character})]))]))
    == Maybe.default(&2, U32, Ezjson.as_u32(J.JNum{line}), 0) : U32}

# LAW: a request's character is `position.character`
law request_character_field:
  for doc: J.Json
  for line: String
  for character: String
  {Server.col_of(Ezjson.obj([("textDocument", doc),
    ("position", Ezjson.obj([("line", J.JNum{line}), ("character", J.JNum{character})]))]))
    == Maybe.default(&2, U32, Ezjson.as_u32(J.JNum{character}), 0) : U32}

# LAW: each encoding goes by its name in the spec
law encoding_wire_names:
  for ee: Enc.Enc
  {Enc.name(ee) == enc.wire(ee) : String}

# LAW: the legend lists the spec's token type names, in order
law legend_wire_names:
  for +n: Nat
  {List.get(&2, String, Semantic.legend(), n) == List.get(&2, String, legend.wire(), n) : Maybe<&2, String>}

# LAW: the encoding after a message is settled from its method and its
# `params` member
law encoding_reads_params:
  for +msg: J.Json
  for ee: Enc.Enc
  {Server.encoding.of(msg, ee) == Server.encoding(Server.method(Server.name_of(msg)), Ezjson.get(msg, "params"), ee)
    : Enc.Enc}

# LAW: a rename of a name the document does not bind is refused with LSP's
# RequestFailed, -32803, whatever was asked
law rename_refuses_a_foreign_name:
  for cc: Enc.Cols
  for at: List<&2, Bind.Pos>
  for uri: String
  for name: String
  for new: String
  {Server.rename.of(cc, Nav.Sites{False{}, at}, uri, name, new)
    == Server.Refusal{"-32803", "only a name bound in this file can be renamed"} : Server.Answer}
