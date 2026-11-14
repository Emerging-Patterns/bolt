# proofs of laws/FindingsSayWhereAndWhat.bend: each def is read for the case
# its law names
import Base
import ../src/finding.bend as F
import ../src/noqa.bend as Noqa
import ../src/rules/table.bend as Table
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/correctness/escape.bend as Escape
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/style/blank.bend as Blank
import ../src/rules/style/transcong.bend as Transcong
import ../src/rules/style/noqa.bend as NoqaRule
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/thunk.bend as Thunk
import ../src/rules/suspicious/prefix.bend as Prefix
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../src/syntax/lex.bend as Lex
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/foreign.bend as Foreign
import ../src/rules/laws/closed.bend as Closed
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/style/reach.bend as Reach
import ../src/rules/style/doc.bend as Doc
import ../laws/FindingsSayWhereAndWhat.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

def Laws.table_cites_get(_path, _line, _col, _len):
  {==}

def Laws.table_cites_set(_path, _line, _col, _len):
  {==}

def Laws.arms_cites_covered_arm(_line, _path, _ll, _cc, _more):
  {==}

def Laws.arms_passes_uncovered_arm(_path, _ll, _cc, _more):
  {==}

def Laws.pick_cites_tail_search(_ll, _cc, _name, _path):
  {==}

def Laws.pick_cites_other_search(_ll, _cc, _name, _path):
  {==}

def Laws.blank_says_the_test(_xx):
  {==}

def Laws.blank_cites_test(_xx, _path, _ll, _cc, _more):
  {==}

def Laws.blank_passes_no_test(_path, _ll, _cc, _more):
  {==}

def Laws.transcong_cites_trans(_ll, _cc, _path):
  {==}

def Laws.noqa_cites_bare_mark(_line, _col, _len, _whole, _path, _gs):
  {==}

def Laws.thunk_cites_self_call(_ll, _cc, _name, _path):
  {==}

def Laws.prefix_cites_run(_msg, _path, _ll, _cc, _more):
  {==}

def Laws.prefix_passes_no_run(_path, _ll, _cc, _more):
  {==}

def Laws.empty_cites_test(_ll, _cc, _msg, _path, _more):
  {==}

def Laws.empty_passes_no_test(_path, _more):
  {==}

def Laws.rewalk_cites_first_site(_name, _line, _col, _len, _path):
  {==}

def Laws.rewalk_reports_once(_name, _line, _col, _len, _path):
  {==}

def Laws.escape_cites_lone_nul(ds, path, line, col, e):
  match ds:
    case Nil{}:
      {==}
    case Con{h, t}:
      Empty.absurd({Escape.finding(h <> t, path, line, col) == F.Finding{path, line, col, 3, "escape",
        "\\0 followed by digits is a NUL character and then those digits, not an octal escape; write \\u{..} instead."} : F.Finding},
        M1.false_true(e))

def Laws.escape_cites_nul_and_digits(ds, path, line, col, e):
  match ds:
    case Nil{}:
      Empty.absurd({Escape.finding(Nil{}, path, line, col)
        == F.Finding{path, line, col, (U32.from_nat(String.length(String.from_list(Nil{}))) + 2 : U32), "escape",
        "\\0" ++ String.from_list(Nil{})
      ++ " is a NUL character followed by \"" ++ String.from_list(Nil{})
      ++ "\", not an octal escape; write \\u{"
      ++ Escape.hex(Escape.value(Nil{}, 0)) ++ "}."} : F.Finding},
        M1.true_false(e))
    case Con{_h, _t}:
      {==}

def Laws.wrap_cites_loose_return(_line, _end, _col, _base, _path, _more):
  {==}

def Laws.wrap_cites_loose_return_or_next(_base, _path, _more):
  {==}

def Laws.wrap_cites_shut_paren(_line, _end, _col, _loose, _base, _path, _more):
  {==}

def Laws.wrap_cites_shut_paren_or_next(_loose, _base, _path, _more):
  {==}

def Laws.wrap_cites_empty_list(_line, _end, _col, _shut, _loose, _base, _path, _more):
  {==}

def Laws.wrap_cites_empty_list_or_next(_shut, _loose, _base, _path, _more):
  {==}

def Laws.wrap_cites_jammed_parameter(_line, _end, _col, _empty, _shut, _loose, _base, _path, _more):
  {==}

def Laws.wrap_cites_jammed_parameter_or_next(_empty, _shut, _loose, _base, _path, _more):
  {==}

def Laws.doc_names_the_item_kind(kk):
  match kk:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

def Laws.unused_names_the_binder_kind(kk):
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

def Laws.closed_names_a_nameless_law(mm):
  match mm:
    case None{}:
      {==}
    case Some{nn}:
      {==}

def Laws.foreign_names_a_nameless_def(mm):
  match mm:
    case None{}:
      {==}
    case Some{nn}:
      {==}

def Laws.noqa_tells_a_bare_mark(_line, _col, _len, _whole, _path, _gs):
  {==}

def Laws.noqa_tells_an_unused_code(code, e):
  %Equal.sym(Bool, NoqaRule.known(code), True{}, e) :
    {Bool.pick(String, _, "`# noqa: " ++ code ++ "` silences nothing on this line.",
      "`# noqa: " ++ code ++ "` is no rule's code, so it silences nothing.")
      == "`# noqa: " ++ code ++ "` silences nothing on this line." : String}
  {==}

def Laws.noqa_tells_an_unknown_code(code, e):
  %Equal.sym(Bool, NoqaRule.known(code), False{}, e) :
    {Bool.pick(String, _, "`# noqa: " ++ code ++ "` silences nothing on this line.",
      "`# noqa: " ++ code ++ "` is no rule's code, so it silences nothing.")
      == "`# noqa: " ++ code ++ "` is no rule's code, so it silences nothing." : String}
  {==}

def Laws.empty_says_the_list_test(_xx):
  {==}

def Laws.empty_says_the_string_test(_xx):
  {==}

def Laws.prefix_says_the_take(_ss, _kk, _lit):
  {==}

def Laws.prefix_writes_a_comma(_tt):
  {==}

def Laws.prefix_writes_an_operator(_tt):
  {==}

def Laws.reach_says_the_name_and_limit(_nm, _max):
  {==}

def Laws.reach_cites_the_binder(_nm, _line, _col, _path, _max, _more):
  {==}
