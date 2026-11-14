# proofs of laws/RulesReadTokensAndChains.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/finding.bend as F
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/table.bend as Table
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/correctness/escape.bend as Escape
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/perf/strings.bend as Strings
import ../src/rules/style/blank.bend as Blank
import ../src/rules/style/space.bend as Space
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/RulesReadTokensAndChains.bend as Laws
import ../laws/defs/Chains.bend as D2
import ./lemmas/BoolEmptiness.bend as M1

# a branch taken lazily is the pick of its two sides
law rh.either:
  for c: Bool
  for -x: List<&2, Lex.Tok>
  for -y: List<&2, Lex.Tok>
  {Lazy.either(List<&2, Lex.Tok>, c, _u => x, _v => y) == Bool.pick(List<&2, Lex.Tok>, c, x, y) : List<&2, Lex.Tok>}

def rh.either(c, _x, _y):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# an and that stops at the first False is the plain and
law rh.and_then:
  for c: Bool
  for -x: Bool
  {Lazy.and_then(c, _u => x) == Bool.and(c, x) : Bool}

def rh.and_then(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a count that stops at zero when a test fails is the pick the other way round
law rh.stop_not:
  for c: Bool
  for -x: Nat
  {Lazy.stop(Nat, Bool.not(c), 0n, _u => x) == Bool.pick(Nat, c, x, 0n) : Nat}

def rh.stop_not(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.arms_ended_at_colon(_t, _l, _c, _rest):
  {==}

def Laws.arms_ended_passes_other(h, rest, e):
  match h:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      match k:
        case Lex.TName{}:
          {==}
        case Lex.TUpper{}:
          {==}
        case Lex.TDotted{}:
          {==}
        case Lex.TWild{}:
          {==}
        case Lex.TKey{}:
          {==}
        case Lex.TNum{}:
          {==}
        case Lex.TStr{}:
          {==}
        case Lex.TChar{}:
          {==}
        case Lex.TComment{}:
          {==}
        case Lex.TSpace{}:
          {==}
        case Lex.TNewline{}:
          {==}
        case Lex.TOp{}:
          {==}
        case Lex.TColon{}:
          Empty.absurd({Arms.ended(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest})
            == Arms.ended(rest) : Bool},
            M1.true_false(e))
        case Lex.TEq{}:
          {==}
        case Lex.TBind{}:
          {==}
        case Lex.TArrow{}:
          {==}
        case Lex.TLam{}:
          {==}
        case Lex.TAll{}:
          {==}
        case Lex.TAmp{}:
          {==}
        case Lex.TOpen{}:
          {==}
        case Lex.TClose{}:
          {==}
        case Lex.TComma{}:
          {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{_a, _b}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.arms_ended_needs_colon(pat, e):
  match pat:
    case Tree.NCons{h, r}:
      Empty.absurd({Arms.ended(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.arms_opens_as_kind_and_text(_want, _tt, _text):
  {==}

def Laws.arms_opens_plus_first(_k, _t, _l, _c, _rest):
  {==}

def Laws.arms_opens_plus_needs_token(toks, e):
  match toks:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Arms.opens.plus(toks) == False{} : Bool}, M1.false_true(e))

def Laws.arms_skip_after_item(_rest):
  {==}

def Laws.arms_skip_after_word(_rest):
  {==}

def Laws.arms_told_needs_wide_arm(aa):
  match aa:
    case Arms.APlus{_j, _t, _l, _c, _n}:
      {==}
    case Arms.ALit{_m, _l, _c, _n}:
      {==}
    case Arms.AOther{}:
      {==}

def Laws.arms_told_skips_other_arms(w2):
  match w2:
    case Arms.Wide{_k, _text}:
      {==}

def Laws.escape_sym_by_code(_x):
  {==}

def Laws.escape_syms_in_order(_c, _t):
  {==}

def Laws.pick_lone_is_one_leaf(_k, _t, _l, _c, _rest, _xx):
  {==}

def Laws.pick_lone_needs_a_chain(nn, xx, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Pick.search.lone(Tree.NCons{h, r}, xx) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.strings_closes_reads_escapes(_ch, _rest, _esc, _shut):
  {==}

def Laws.strings_closes_at_the_end(_esc, _shut):
  {==}

def Laws.strings_opened_past_first_char(_q, _rest):
  {==}

def Laws.strings_opened_needs_chars(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Strings.opened(cs) == False{} : Bool}, M1.false_true(e))

def Laws.blank_lit_is_two_quotes(kk, _tt):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.blank_name_either_side(_ka, _ta, _kb, _tb):
  {==}

def Laws.space_unimported_keeps_newline(_t, _l, _c, _rest, _start, _cutting):
  {==}

def Laws.space_unimported_cuts_import_lines(k, t, l, c, rest, start, cutting, e):
  match k:
    case Lex.TName{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TName{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TUpper{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TUpper{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TDotted{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TDotted{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TWild{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TWild{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TKey{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TKey{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TNum{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TNum{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TStr{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TStr{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TChar{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TChar{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TComment{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TComment{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TSpace{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TSpace{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TNewline{}:
      Empty.absurd({Space.unimported(Lex.Tok{Lex.TNewline{}, t, l, c} <> rest, start, cutting)
        == Bool.pick(List<&2, Lex.Tok>, Bool.or(cutting, Bool.and(start, String.eq(t, "import"))),
          Space.unimported(rest, False{}, True{}),
          Lex.Tok{Lex.TNewline{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
        : List<&2, Lex.Tok>}, M1.true_false(e))
    case Lex.TOp{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TOp{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TColon{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TColon{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TEq{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TEq{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TBind{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TBind{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TArrow{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TArrow{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TLam{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TLam{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TAll{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TAll{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TAmp{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TAmp{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TOpen{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TOpen{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TClose{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TClose{}, t, l, c} <> Space.unimported(rest, False{}, False{}))
    case Lex.TComma{}:
      rh.either(Bool.or(cutting, Bool.and(start, String.eq(t, "import"))), Space.unimported(rest, False{}, True{}),
        Lex.Tok{Lex.TComma{}, t, l, c} <> Space.unimported(rest, False{}, False{}))

def Laws.wrap_gt_chars_each(c, t):
  rh.and_then(Char.is_eq(c, '>'), Wrap.check.gt_chars(t))

def Laws.wrap_gt_chars_of_none(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Wrap.check.gt_chars(cs) == True{} : Bool}, M1.false_true(e))

def Laws.wrap_all_gt_not_empty(_tx):
  {==}

def Laws.wrap_ticks_of_run(tx):
  rh.stop_not(Wrap.check.all_gt(tx), Wrap.check.gt_count(String.to_list(tx)))

def Laws.wrap_angle_opens_when_glued(_glued, _tx):
  {==}

def Laws.wrap_separators(act):
  match act:
    case Wrap.AOpen{}:
      {==}
    case Wrap.AParen{}:
      {==}
    case Wrap.AEnd{}:
      {==}
    case Wrap.AUnparen{}:
      {==}
    case Wrap.ABrack{}:
      {==}
    case Wrap.AUnbrack{}:
      {==}
    case Wrap.ABrace{}:
      {==}
    case Wrap.AUnbrace{}:
      {==}
    case Wrap.AAngle{}:
      {==}
    case Wrap.AUnangle{}:
      {==}
    case Wrap.AComma{}:
      {==}
    case Wrap.AArrow{}:
      {==}
    case Wrap.AStray{}:
      {==}
    case Wrap.ANone{}:
      {==}

def Laws.concat_plus_first_operator(_h, _rest):
  {==}

def Laws.concat_plus_needs_a_chain(pp, e):
  match pp:
    case Tree.NCons{h, r}:
      Empty.absurd({Concat.plus(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.table_top_has_skips_groups(_open, _kids, _close, _rest, _want):
  {==}

def Laws.table_top_has_reads_leaves(_k, _t, _l, _c, _rest, _want):
  {==}

def Laws.table_top_has_needs_a_chain(nn, want, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Table.top_has(Tree.NCons{h, r}, want) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.table_array_sized_needs_a_chain(nn, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Table.array_sized(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.table_built_needs_a_chain(nn, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Table.built(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.table_lone_num_one_number(_t, _l, _c):
  {==}

def Laws.table_lone_num_needs_a_chain(nn, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Table.lone_num(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.table_range_count_last_argument(_h):
  {==}

def Laws.table_range_count_needs_arguments(as, e):
  match as:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Table.range_count(as) == False{} : Bool}, M1.false_true(e))

def Laws.table_hits_get_and_set(_open, _tt, _kids, _fixed, _path, _line, _col):
  {==}

def Laws.empty_close_here_at_depth_zero(kk):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_close_here_not_deeper(kk, _p):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_kept_once_found(_k, _t, _l, _c, _rest, _xx, _dd, _live):
  {==}

def Laws.empty_kept_stops_at_close(_k, _t, _l, _c, _rest, _xx, _dd):
  {==}

def Laws.empty_kept_reads_on(_k, _t, _l, _c, _rest, _xx, _dd):
  {==}

def Laws.empty_kept_at_the_end(_xx, _dd, _found, _live):
  {==}

def Laws.empty_proofy_head_colon(_k2, _t2):
  {==}

def Laws.empty_proofy_head_arrow(_k2, _t2):
  {==}

def Laws.empty_proofy_head_other(k1, k2, t2, e):
  match k1:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      Empty.absurd({Empty.proofy.head(Lex.TColon{}, k2, t2) == False{} : Bool}, M1.true_false(e))
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      Empty.absurd({Empty.proofy.head(Lex.TArrow{}, k2, t2) == False{} : Bool}, M1.true_false(e))
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_proofy_end_two_tokens(_k1, _t1, _l1, _c1, _k2, _t2, _l2, _c2, _rest):
  {==}

def Laws.empty_proofy_end_one_token(_k1, _t1, _l1, _c1):
  {==}

def Laws.empty_proofy_end_needs_token(toks, e):
  match toks:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Empty.proofy.end(toks) == False{} : Bool}, M1.false_true(e))

def Laws.empty_proofy_fin_at_depth_one(kk):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_proofy_fin_not_at_zero(kk):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_proofy_fin_not_deeper(kk, _p):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

def Laws.empty_proofy_decides_after_parameters(_k, _t, _l, _c, _rest, _dd):
  {==}

def Laws.empty_proofy_reads_on(_k, _t, _l, _c, _rest, _dd):
  {==}

def Laws.empty_proofy_needs_tokens(toks, dd, fin, e):
  match toks:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Empty.proofy(toks, dd, fin) == False{} : Bool}, M1.false_true(e))

def Laws.empty_item_other_by_keyword(_word, _skip):
  {==}

def Laws.arms_told_plus_from_k(_kk, _text, _jj, _tt, _ll, _cc, _nn):
  {==}

def Laws.arms_told_literal_from_k(_kk, _text, _mm, _ll, _cc, _nn):
  {==}

def Laws.arms_plus_is_no_part(_more):
  {==}

def Laws.arms_cons_is_a_part(_more):
  {==}

def Laws.arms_other_operator_is_bad(tt, more, e1, e2):
  %Equal.sym(Bool, String.eq(tt, "+"), False{}, e1) :
    {Bool.pick(List<&2, Arms.Part>, _, more,
      Bool.pick(Arms.Part, String.eq(tt, "<>"), Arms.PCons{}, Arms.PBad{}) <> more)
      == Arms.PBad{} <> more : List<&2, Arms.Part>}
  %Equal.sym(Bool, String.eq(tt, "<>"), False{}, e2) :
    {Bool.pick(Arms.Part, _, Arms.PCons{}, Arms.PBad{}) <> more == Arms.PBad{} <> more : List<&2, Arms.Part>}
  {==}

def Laws.concat_uses_counts_the_name(tt, _ll, _cc, name, e):
  %Equal.sym(Bool, String.eq(tt, name), True{}, e) : {Bool.pick(Nat, _, 1n, 0n) == 1n : Nat}
  {==}

def Laws.concat_uses_skips_other_names(tt, _ll, _cc, name, e):
  %Equal.sym(Bool, String.eq(tt, name), False{}, e) : {Bool.pick(Nat, _, 1n, 0n) == 0n : Nat}
  {==}

def Laws.table_drop_takes_the_name(hh, rest, nm, e):
  %Equal.sym(Bool, String.eq(hh, nm), True{}, e) :
    {Bool.pick(List<&2, String>, _, Table.drop(rest, nm), hh <> Table.drop(rest, nm))
      == Table.drop(rest, nm) : List<&2, String>}
  {==}

def Laws.table_drop_keeps_other_names(hh, rest, nm, e):
  %Equal.sym(Bool, String.eq(hh, nm), False{}, e) :
    {Bool.pick(List<&2, String>, _, Table.drop(rest, nm), hh <> Table.drop(rest, nm))
      == hh <> Table.drop(rest, nm) : List<&2, String>}
  {==}

def Laws.wrap_gt_run_closes_angles(tx, glued, e):
  %Equal.sym(Bool, Wrap.check.all_gt(tx), True{}, e) :
    {Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Bool.pick(Wrap.Act, _, Wrap.AUnangle{}, Wrap.ANone{}))
      == Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Wrap.AUnangle{}) : Wrap.Act}
  {==}

def Laws.wrap_other_operator_moves_no_angle(tx, glued, e):
  %Equal.sym(Bool, Wrap.check.all_gt(tx), False{}, e) :
    {Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Bool.pick(Wrap.Act, _, Wrap.AUnangle{}, Wrap.ANone{}))
      == Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Wrap.ANone{}) : Wrap.Act}
  {==}

def Laws.pick_search_text_of_a_leaf(_kk, _tt, _ll, _cc):
  {==}

def Laws.pick_search_text_of_a_group(_kk, _oo, _ll, _cc, _kids, _cl):
  {==}

def Laws.table_key_is_name_and_place(_tt, _line, _col):
  {==}
