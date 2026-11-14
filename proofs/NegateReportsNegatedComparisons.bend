# proofs of laws/NegateReportsNegatedComparisons.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/rules/tokens.bend as T
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/style/negate.bend as Negate
import ../laws/NegateReportsNegatedComparisons.bend as Laws
import ../laws/RoleLawFileNamed.bend as L1
import ./lemmas/RoleLawFilePicked.bend as M1
import ./lemmas/LawFileExemptions.bend as M2

# negate (laws/NegateReportsNegatedComparisons.bend). Base states each comparison as a test of
# one three-way compare, so each negation is settled by the three answers
# of a compare; the rule's table is read name by name; the walk adds one
# finding exactly where a token has a word.

# not not is the test itself
law neg.not_not:
  for x: Bool
  {Bool.not(Bool.not(x)) == x : Bool}

def neg.not_not(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# not less is greater or equal
law neg.lt:
  for c: Cmp
  {Bool.not(Cmp.is_lt(c)) == Cmp.is_ge(c) : Bool}

def neg.lt(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# not less or equal is greater
law neg.le:
  for c: Cmp
  {Bool.not(Cmp.is_le(c)) == Cmp.is_gt(c) : Bool}

def neg.le(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# not greater is less or equal
law neg.gt:
  for c: Cmp
  {Bool.not(Cmp.is_gt(c)) == Cmp.is_le(c) : Bool}

def neg.gt(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# not greater or equal is less
law neg.ge:
  for c: Cmp
  {Bool.not(Cmp.is_ge(c)) == Cmp.is_lt(c) : Bool}

def neg.ge(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.negated_u32_is_its_word(s, a, b):
  match s:
    case Laws.Eq{}:
      {==}
    case Laws.Ne{}:
      neg.not_not(Cmp.is_eq(U32.cmp(a, b)))
    case Laws.Lt{}:
      neg.lt(U32.cmp(a, b))
    case Laws.Le{}:
      neg.le(U32.cmp(a, b))
    case Laws.Gt{}:
      neg.gt(U32.cmp(a, b))
    case Laws.Ge{}:
      neg.ge(U32.cmp(a, b))

def Laws.negated_nat_is_its_word(s, a, b):
  match s:
    case Laws.Eq{}:
      {==}
    case Laws.Ne{}:
      neg.not_not(Cmp.is_eq(Nat.cmp(a, b)))
    case Laws.Lt{}:
      neg.lt(Nat.cmp(a, b))
    case Laws.Le{}:
      neg.le(Nat.cmp(a, b))
    case Laws.Gt{}:
      neg.gt(Nat.cmp(a, b))
    case Laws.Ge{}:
      neg.ge(Nat.cmp(a, b))

def Laws.opposite_names_flip(s):
  match s:
    case Laws.Eq{}:
      {==}
    case Laws.Ne{}:
      {==}
    case Laws.Lt{}:
      {==}
    case Laws.Le{}:
      {==}
    case Laws.Gt{}:
      {==}
    case Laws.Ge{}:
      {==}

def Laws.opposite_needs_comparison(op, e1, e2, e3, e4, e5, e6):
  s1 = Equal.sym(Bool, String.eq(op, "is_eq"), False{}, e1)
  %s1 : {Bool.pick(String, _, "is_ne",
      Bool.pick(String, String.eq(op, "is_ne"), "is_eq",
        Bool.pick(String, String.eq(op, "is_lt"), "is_ge",
          Bool.pick(String, String.eq(op, "is_ge"), "is_lt",
            Bool.pick(String, String.eq(op, "is_gt"), "is_le",
              Bool.pick(String, String.eq(op, "is_le"), "is_gt", "")))))) == "" : String}
  s2 = Equal.sym(Bool, String.eq(op, "is_ne"), False{}, e2)
  %s2 : {Bool.pick(String, _, "is_eq",
      Bool.pick(String, String.eq(op, "is_lt"), "is_ge",
        Bool.pick(String, String.eq(op, "is_ge"), "is_lt",
          Bool.pick(String, String.eq(op, "is_gt"), "is_le", Bool.pick(String, String.eq(op, "is_le"), "is_gt", "")))))
    == "" : String}
  s3 = Equal.sym(Bool, String.eq(op, "is_lt"), False{}, e3)
  %s3 : {Bool.pick(String, _, "is_ge",
      Bool.pick(String, String.eq(op, "is_ge"), "is_lt",
        Bool.pick(String, String.eq(op, "is_gt"), "is_le", Bool.pick(String, String.eq(op, "is_le"), "is_gt", ""))))
    == "" : String}
  s4 = Equal.sym(Bool, String.eq(op, "is_ge"), False{}, e4)
  %s4 : {Bool.pick(String, _, "is_lt",
      Bool.pick(String, String.eq(op, "is_gt"), "is_le", Bool.pick(String, String.eq(op, "is_le"), "is_gt", "")))
    == "" : String}
  s5 = Equal.sym(Bool, String.eq(op, "is_gt"), False{}, e5)
  %s5 : {Bool.pick(String, _, "is_le", Bool.pick(String, String.eq(op, "is_le"), "is_gt", "")) == "" : String}
  s6 = Equal.sym(Bool, String.eq(op, "is_le"), False{}, e6)
  %s6 : {Bool.pick(String, _, "is_gt", "") == "" : String}
  {==}

def Laws.word_of_u32_comparison(s):
  match s:
    case Laws.Eq{}:
      {==}
    case Laws.Ne{}:
      {==}
    case Laws.Lt{}:
      {==}
    case Laws.Le{}:
      {==}
    case Laws.Gt{}:
      {==}
    case Laws.Ge{}:
      {==}

def Laws.word_of_nat_comparison(s):
  match s:
    case Laws.Eq{}:
      {==}
    case Laws.Ne{}:
      {==}
    case Laws.Lt{}:
      {==}
    case Laws.Le{}:
      {==}
    case Laws.Gt{}:
      {==}
    case Laws.Ge{}:
      {==}

def Laws.word_needs_u32_or_nat(t, e, o):
  s = Equal.sym(Bool, String.starts_with(t, "U32."), False{}, e)
  %s : {Bool.pick(String, _, Negate.under("U32", String.drop(t, 4n)),
      Bool.pick(String, String.starts_with(t, "Nat."), Negate.under("Nat", String.drop(t, 4n)), "")) == "" : String}
  r = Equal.sym(Bool, String.starts_with(t, "Nat."), False{}, o)
  %r : {Bool.pick(String, _, Negate.under("Nat", String.drop(t, 4n)), "") == "" : String}
  {==}

def Laws.under_needs_comparison(ty, op, e):
  s = Equal.sym(Bool, String.is_empty(Negate.opposite(op)), True{}, e)
  %s : {Bool.pick(String, _, "", ty ++ "." ++ Negate.opposite(op)) == "" : String}
  {==}

# a finding is added exactly when the token has a word
law neg.hit:
  for none: Bool
  for -w: String
  for -path: String
  for -l: U32
  for -c: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Negate.hit.go(none, w, path, l, c, more)) == Bool.pick(Nat, none, m, 1n+m) : Nat}

def neg.hit(none, _w, _path, _l, _c, more, m, ih):
  match none:
    case True{}:
      ih
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

def Laws.negate_counts(toks, path, skip):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      neg.hit(String.is_empty(Negate.found(sk, k, t, rest)), Negate.found(sk, k, t, rest), path, l, c,
        Negate.walk(rest, path, sk), Laws.negated(rest, sk), Laws.negate_counts(rest, path, sk))

def Laws.negate_cites_bool_not(_w, _path, _l, _c):
  {==}

def Laws.negate_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Negate.walk(T.sig(toks), path, False{})) == Nil{}
    : List<&2, F.Finding>}
  {==}

def Laws.role_negate(path, _text, toks, _tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Negate.walk(T.sig(toks), path, False{})),
    Role.is_law_file(Role.of_path(path)), Paths.is_law_file(path),
    L1.role_law_file_named(path))

def Laws.role_negate_exempt(r, e, path, _text, toks, _tree, _bound, _items):
  M2.ex.stop(Role.is_law_file(r), e, _u => Negate.walk(T.sig(toks), path, False{}))

def Laws.found_skips_proofs(_k, _t, _rest):
  {==}

def Laws.found_needs_bool_not(k, t, rest, e):
  s = Equal.sym(Bool, Negate.named(k, t), False{}, e)
  %s : {Negate.found.go(_, rest) == "" : String}
  {==}

def Laws.found_reads_after_bool_not(_rest):
  {==}

def Laws.at_reads_negated_call(_l1, _c1, t2, _l2, _c2, _l3, _c3, rest, e):
  s = Equal.sym(Bool, Negate.ends(Negate.shut(rest, 0n, False{})), True{}, e)
  %s : {Negate.at.go(_, Negate.word(t2)) == Negate.word(t2) : String}
  {==}

def Laws.at_needs_closing_bracket_next(_l1, _c1, t2, _l2, _c2, _l3, _c3, rest, e):
  s = Equal.sym(Bool, Negate.ends(Negate.shut(rest, 0n, False{})), False{}, e)
  %s : {Negate.at.go(_, Negate.word(t2)) == "" : String}
  {==}

# anything and False is False
law neg.and_f:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def neg.and_f(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.at_needs_dotted_name(k1, t1, _l1, _c1, t2, _l2, _c2, _k3, _t3, _l3, _c3, _rest):
  a = Equal.sym(Bool, Bool.and(String.eq(Empty.code(k1, t1), "("), False{}), False{},
    neg.and_f(String.eq(Empty.code(k1, t1), "(")))
  %a : {Negate.at.go(_, Negate.word(t2)) == "" : String}
  {==}

def Laws.at_needs_call(_l1, _c1, t2, _l2, _c2, k3, t3, _l3, _c3, rest, e):
  s = Equal.sym(Bool, String.eq(Empty.code(k3, t3), "("), False{}, e)
  %s : {Negate.at.go(Bool.and(_, Negate.ends(Negate.shut(rest, 0n, False{}))), Negate.word(t2)) == "" : String}
  {==}

def Laws.at_needs_arguments_closed(_l1, _c1, _t2, _l2, _c2, _l3, _c3):
  {==}

def Laws.at_needs_token_after_call(_l1, _c1, _t2, _l2, _c2, _l3, _c3, _t4, _l4, _c4):
  {==}

def Laws.named_skips_string(_t):
  {==}

def Laws.named_skips_comment(_t):
  {==}

def Laws.shut_stops_at_close(toks, _d):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{_k, _t, _l, _c}, _rest}:
      {==}

def Laws.shut_closes_at_depth_zero(_t, _l, _c, rest):
  Laws.shut_stops_at_close(rest, 0n)

def Laws.shut_counts_opening_bracket(_t, _l, _c, _rest, _d):
  {==}

def Laws.shut_passes_inner_close(_t, _l, _c, _rest, _d):
  {==}

def Laws.shut_passes_comma(_t, _l, _c, _rest, _d):
  {==}

def Laws.shut_runs_out(_d):
  {==}

def Laws.ends_at_closing_bracket(_l, _c, _rest):
  {==}

def Laws.ends_not_at_operator(_l, _c, _rest):
  {==}
