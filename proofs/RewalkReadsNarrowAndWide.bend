# proofs of laws/RewalkReadsNarrowAndWide.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../laws/RewalkReadsNarrowAndWide.bend as Laws
import ../laws/defs/Chains.bend as D2
import ./lemmas/BoolEmptiness.bend as M1

def Laws.name_hit_other_name(_slot):
  {==}

def Laws.name_hit_same_name(slot):
  match slot:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.either_joins_reads(_w1, _s1, _w2, _s2):
  {==}

def Laws.slot_by_accessor_family(list, str, arr):
  match list:
    case True{}:
      {==}
    case False{}:
      match str:
        case True{}:
          {==}
        case False{}:
          match arr:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.slot_of_named_accessors(_tt):
  {==}

def Laws.step_is_zero_of_none_left(pp, e):
  %Equal.sym(Nat, pp, 0n, e) : {Rewalk.step_is_zero(_) == True{} : Bool}
  {==}

def Laws.step_is_zero_of_some_left(_k):
  {==}

def Laws.step_hot_live_counts_down(_p):
  {==}

def Laws.step_hot_live_of_none_left(left, e):
  %Equal.sym(Nat, left, 0n, e) : {Rewalk.step_hot_live(_) == False{} : Bool}
  {==}

def Laws.here_call_callee_is_wide(_tt, _name, _hot):
  {==}

def Laws.here_call_mention_keeps_slot(_tt, _name, _hot):
  {==}

def Laws.here_hit_index_is_narrow(_call, _tt, _name, _hot):
  {==}

def Laws.here_hit_otherwise_call(_call, _tt, _name, _hot):
  {==}

def Laws.inner_hot_call_cold(_hot):
  {==}

def Laws.inner_hot_call_keeps(_hot):
  {==}

def Laws.inner_hot_bracket_cold(_call, _hot):
  {==}

def Laws.inner_hot_otherwise_call(_call, _hot):
  {==}

def Laws.inner_live_call_of_accessor(_tt):
  {==}

def Laws.inner_live_call_needs_call(_tt):
  {==}

def Laws.inner_live_bracket_counts_none(_call, _tt):
  {==}

def Laws.inner_live_otherwise_call(_call, _tt):
  {==}

def Laws.has_eq_at_equals(_t, _l, _c, _rest):
  {==}

def Laws.has_eq_passes_other(h, rest, e):
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
          {==}
        case Lex.TEq{}:
          Empty.absurd({Rewalk.has_eq(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest})
            == Rewalk.has_eq(rest) : Bool}, M1.true_false(e))
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

def Laws.has_eq_needs_a_chain(nn, e):
  match nn:
    case Tree.NCons{h, r}:
      Empty.absurd({Rewalk.has_eq(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.pick_hot_skips_left_side(_brack, _call, _hot):
  {==}

def Laws.pick_hot_otherwise_inner(_brack, _call, _hot):
  {==}

def Laws.pick_live_skips_left_side(_brack, _call, _tt):
  {==}

def Laws.pick_live_otherwise_inner(_brack, _call, _tt):
  {==}

def Laws.narrow_let_only_narrow_reads(_wide, _slot):
  {==}

def Laws.expensive_walk_or_loop(_tt, _self, _lp):
  {==}

def Laws.indexed_by_bracket(_k, _o, _l, _c, _kids, _close, _tail):
  {==}

def Laws.indexed_needs_a_chain(rest, e):
  match rest:
    case Tree.NCons{h, r}:
      Empty.absurd({Rewalk.indexed(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.before_by_line_then_column(_l1, _c1, _l2, _c2):
  {==}

def Laws.add_seen_first_name(_extra, _field, _nm, _tt):
  {==}

def Laws.add_seen_second_name(_extra, _field, _nm, _tt):
  {==}

def Laws.fold_names_marks_field(_t, _l, _c, _rest, _seen, _extra, _field, _nm):
  {==}

def Laws.note_from_one_name(_seen, _extra, _field, _nm, _rhs):
  {==}

def Laws.note_st_reads_both_sides(_kids):
  {==}
