# proofs of laws/NumeralReportsConvertedLiterals.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/rules/tokens.bend as T
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/style/numeral.bend as Numeral
import ../laws/NumeralReportsConvertedLiterals.bend as Laws
import ../laws/RoleLawFileNamed.bend as L1
import ./lemmas/RoleLawFilePicked.bend as M1
import ./lemmas/LawFileExemptions.bend as M2

# numeral (laws/NumeralReportsConvertedLiterals.bend). The walk adds one finding exactly where a
# token opens a conversion; the shape is read off its three tokens, each
# test from one hypothesis.

# anything and False is False
law num.and_f:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def num.and_f(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a finding is added exactly when the token opens a conversion
law num.hit:
  for none: Bool
  for -ds: String
  for -path: String
  for -l: U32
  for -c: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Numeral.hit.go(none, ds, path, l, c, more)) == Bool.pick(Nat, none, m, 1n+m) : Nat}

def num.hit(none, _ds, _path, _l, _c, more, m, ih):
  match none:
    case True{}:
      ih
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

def Laws.numeral_counts(toks, path, skip):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      num.hit(String.is_empty(Numeral.found(sk, k, t, rest)), Numeral.found(sk, k, t, rest), path, l, c,
        Numeral.walk(rest, path, sk), Laws.converted(rest, sk), Laws.numeral_counts(rest, path, sk))

def Laws.numeral_cites_conversion(_ds, _path, _l, _c):
  {==}

def Laws.numeral_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Numeral.walk(T.sig(toks), path, False{})) == Nil{}
    : List<&2, F.Finding>}
  {==}

def Laws.role_numeral(path, _text, toks, _tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Numeral.walk(T.sig(toks), path, False{})),
    Role.is_law_file(Role.of_path(path)), Paths.is_law_file(path),
    L1.role_law_file_named(path))

def Laws.role_numeral_exempt(r, e, path, _text, toks, _tree, _bound, _items):
  M2.ex.stop(Role.is_law_file(r), e, _u => Numeral.walk(T.sig(toks), path, False{}))

def Laws.found_skips_proofs(_k, _t, _rest):
  {==}

def Laws.found_needs_to_nat(k, t, rest, e):
  s = Equal.sym(Bool, Numeral.named(k, t), False{}, e)
  %s : {Numeral.found.go(_, rest) == "" : String}
  {==}

def Laws.found_reads_after_to_nat(_rest):
  {==}

def Laws.named_skips_string(_t):
  {==}

def Laws.named_skips_comment(_t):
  {==}

def Laws.at_reads_literal(_l1, _c1, t2, _l2, _c2, _l3, _c3, _rest, e):
  s = Equal.sym(Bool, Numeral.digits(t2), True{}, e)
  %s : {Bool.pick(String, _, t2, "") == t2 : String}
  {==}

def Laws.at_needs_digits_alone(_l1, _c1, t2, _l2, _c2, _l3, _c3, _rest, e):
  s = Equal.sym(Bool, Numeral.digits(t2), False{}, e)
  %s : {Bool.pick(String, _, t2, "") == "" : String}
  {==}

# with no digits there is nothing, brackets or not
law num.go_empty:
  for ok: Bool
  {Numeral.at.go(ok, "") == "" : String}

def num.go_empty(ok):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.at_needs_number(k1, t1, _l1, _c1, _t2, _l2, _c2, k3, t3, _l3, _c3, _rest):
  num.go_empty(Bool.and(String.eq(Empty.code(k1, t1), "("), String.eq(Empty.code(k3, t3), ")")))

def Laws.at_needs_closing_bracket(_l1, _c1, t2, _l2, _c2, k3, t3, _l3, _c3, _rest, e):
  s = Equal.sym(Bool, String.eq(Empty.code(k3, t3), ")"), False{}, e)
  %s : {Numeral.at.go(_, Numeral.literal(Lex.TNum{}, t2)) == "" : String}
  {==}

def Laws.at_needs_opening_bracket(k1, t1, _l1, _c1, t2, _l2, _c2, _l3, _c3, _rest, e):
  s = Equal.sym(Bool, String.eq(Empty.code(k1, t1), "("), False{}, e)
  %s : {Numeral.at.go(Bool.and(_, True{}), Numeral.literal(Lex.TNum{}, t2)) == "" : String}
  {==}

def Laws.digits_needs_every_char(t, e):
  s = Equal.sym(Bool, Numeral.digits.all(String.to_list(t)), False{}, e)
  %s : {Bool.and(Bool.not(String.is_empty(t)), _) == False{} : Bool}
  num.and_f(Bool.not(String.is_empty(t)))

def Laws.digits_all_reads_each(c, rest, e):
  s = Equal.sym(Bool, Char.is_digit(c), True{}, e)
  %s : {Lazy.and_then(_, _u => Numeral.digits.all(rest)) == Numeral.digits.all(rest) : Bool}
  {==}

def Laws.digits_all_holds_of_one_digit(c, e):
  s = Equal.sym(Bool, Char.is_digit(c), True{}, e)
  %s : {Lazy.and_then(_, _u => Numeral.digits.all(Nil{})) == True{} : Bool}
  {==}

def Laws.digits_all_stops_at_other_char(c, rest, e):
  s = Equal.sym(Bool, Char.is_digit(c), False{}, e)
  %s : {Lazy.and_then(_, _u => Numeral.digits.all(rest)) == False{} : Bool}
  {==}

def Laws.literal_takes_digits(t, e):
  s = Equal.sym(Bool, Numeral.digits(t), True{}, e)
  %s : {Bool.pick(String, _, t, "") == t : String}
  {==}
