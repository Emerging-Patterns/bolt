# proofs of laws/LspRepliesFollowTheProtocol.bend: each reply by evaluation;
# a choice by rewriting it with what the law assumes, or case by case
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/frame.bend as Frame
import ../src/syntax/bind.bend as Bind
import ../src/config.bend as Config
import ../src/lsp/proto.bend as Proto
import ../src/codes.bend as Codes
import ../laws/LspRepliesFollowTheProtocol.bend as Laws

def Laws.rpc_response(_id, _result):
  {==}

def Laws.rpc_failure(_id, _code, _message):
  {==}

def Laws.rpc_notify(_method, _params):
  {==}

def Laws.position_fields(_line, _character):
  {==}

def Laws.diagnostic_fields(_cc, _line, _msg):
  {==}

def Laws.finding_range_named(cc, line, col, len, e):
  %Equal.sym(Bool, U32.is_eq(len, 0), False{}, e) :
    {Ezjson.obj([("start", Proto.position(cc, line, col)),
      ("end", Bool.pick(J.Json, _, Proto.position(cc, (line + 1 : U32), 0),
        Proto.position(cc, line, (col + len : U32))))])
      == Laws.range(Proto.position(cc, line, col), Proto.position(cc, line, (col + len : U32))) : J.Json}
  {==}

def Laws.finding_range_rest_of_line(cc, line, col, len, e):
  %Equal.sym(Bool, U32.is_eq(len, 0), True{}, e) :
    {Ezjson.obj([("start", Proto.position(cc, line, col)),
      ("end", Bool.pick(J.Json, _, Proto.position(cc, (line + 1 : U32), 0),
        Proto.position(cc, line, (col + len : U32))))])
      == Laws.range(Proto.position(cc, line, col), Proto.position(cc, (line + 1 : U32), 0)) : J.Json}
  {==}

def Laws.finding_fields(_cc, level, _path, _line, _col, _len, _rule, _msg):
  match level:
    case Config.Off{}:
      {==}
    case Config.Warn{}:
      {==}
    case Config.Error{}:
      {==}

def Laws.publish_fields(_cc, _uri, _ds, _gs):
  {==}

def Laws.line_range_whole_line(_cc, _line):
  {==}

def Laws.hover_fields(_kk, _name, _line, _sig, _doc, _path):
  {==}

def Laws.hover_text_no_doc(sig, doc, e):
  %Equal.sym(Bool, String.is_empty(doc), True{}, e) :
    {"```bend\n" ++ sig ++ "\n```" ++ Bool.pick(String, _, "", "\n\n" ++ doc) == "```bend\n" ++ sig ++ "\n```" : String}
  {==}

def Laws.hover_text_doc(sig, doc, e):
  %Equal.sym(Bool, String.is_empty(doc), False{}, e) :
    {"```bend\n" ++ sig ++ "\n```" ++ Bool.pick(String, _, "", "\n\n" ++ doc)
      == "```bend\n" ++ sig ++ "\n```" ++ "\n\n" ++ doc : String}
  {==}

def Laws.location_fields(_cc, _uri, _kk, _name, _line, _sig, _doc, _path):
  {==}

def Laws.hover_local_fields(_name, _line, _col, _kind, _note):
  {==}

def Laws.kind_name_words(kk):
  match kk:
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

def Laws.where_bound_line(kk, _line):
  match kk:
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

def Laws.name_range_fields(_cc, _line, _col, _name):
  {==}

def Laws.location_local_fields(_cc, _uri, _name, _line, _col, _kind, _note):
  {==}

def Laws.symbol_fields(_cc, _kk, _name, _line, _sig, _doc, _path):
  {==}

def Laws.completion_fields(_cc, _kk, _name, _ll, _sig, _doc, _path, _line, _start, _col):
  {==}

def Laws.rename_fields(_cc, _uri, _name, _new, _ps):
  {==}

def Laws.semantic_fields(_data):
  {==}

def Laws.hex_digit_values(dd):
  match dd:
    case Laws.H0{}:
      {==}
    case Laws.H1{}:
      {==}
    case Laws.H2{}:
      {==}
    case Laws.H3{}:
      {==}
    case Laws.H4{}:
      {==}
    case Laws.H5{}:
      {==}
    case Laws.H6{}:
      {==}
    case Laws.H7{}:
      {==}
    case Laws.H8{}:
      {==}
    case Laws.H9{}:
      {==}
    case Laws.La{}:
      {==}
    case Laws.Lb{}:
      {==}
    case Laws.Lc{}:
      {==}
    case Laws.Ld{}:
      {==}
    case Laws.Le{}:
      {==}
    case Laws.Lf{}:
      {==}
    case Laws.Ua{}:
      {==}
    case Laws.Ub{}:
      {==}
    case Laws.Uc{}:
      {==}
    case Laws.Ud{}:
      {==}
    case Laws.Ue{}:
      {==}
    case Laws.Uf{}:
      {==}

def Laws.path_drops_scheme(rest):
  match rest:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def Laws.path_keeps_other(uri, e):
  %Equal.sym(Bool, String.starts_with(uri, "file://"), False{}, e) :
    {Frame.decode(Proto.unpercent(String.to_list(Bool.pick(String, _, String.drop(uri, 7n), uri))))
      == Frame.decode(Proto.unpercent(String.to_list(uri))) : String}
  {==}

def Laws.source_names_group_and_rule(_ss, _id, _grp):
  {==}

def Laws.source_of_no_rule(mm):
  match mm:
    case None{}:
      {==}
    case Some{ee}:
      match ee:
        case Codes.Entry{ss, id, grp}:
          {==}
