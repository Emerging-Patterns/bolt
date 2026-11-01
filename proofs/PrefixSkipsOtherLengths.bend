# proofs of laws/PrefixSkipsOtherLengths.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../laws/defs/PrefixLength.bend as D1
import ../src/finding.bend as F
import ../src/src.bend as Src
import ../src/rules/suspicious/prefix.bend as Prefix
import ../laws/PrefixReportsTakeComparedToLiteral.bend as L1
import ./PrefixReportsTakeComparedToLiteral.bend as P1
import ../laws/PrefixSkipsOtherLengths.bend as Laws

# the count of a run whose take fails, when it starts the tokens and is the
# take-first one: none
law prefix.none_a:
  for b: Bool
  for e: {b == False{} : Bool}
  {Bool.pick(Nat, Bool.or(b, False{}), 1n, 0n) == 0n : Nat}

def prefix.none_a(b, e):
  %Equal.sym(Bool, b, False{}, e) : {Bool.pick(Nat, Bool.or(_, False{}), 1n, 0n) == 0n : Nat}
  {==}

# the same for the literal-first one
law prefix.none_b:
  for b: Bool
  for e: {b == False{} : Bool}
  {Bool.pick(Nat, b, 1n, 0n) == 0n : Nat}

def prefix.none_b(b, e):
  %Equal.sym(Bool, b, False{}, e) : {Bool.pick(Nat, _, 1n, 0n) == 0n : Nat}
  {==}

def Laws.prefix_skips_take_first(path, e, s, k, lit, l, c, f, text, tree, bound, items):
  +ts = {[Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TNum{}, k, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
    Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TStr{}, lit, l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}]
    : List<&2, Lex.Tok>}
  +m = Bool.pick(Nat, Paths.is_law_file(path), 0n, L1.prefix_count(T.sig(ts)))
  Equal.trans(Nat, List.length(&2, F.Finding, Prefix.check(Src.Src{path, text, ts, tree, bound, items})), m, 0n,
    L1.prefix_counts(path, text, ts, tree, bound, items),
    (%Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {Bool.pick(Nat, _, 0n, L1.prefix_count(T.sig(ts)))
      == 0n : Nat}; prefix.none_a(D1.prefix_fits(k, lit), f)))

def Laws.prefix_skips_literal_first(path, e, s, k, lit, l, c, f, text, tree, bound, items):
  +ts = {[Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TNum{}, k, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}]
    : List<&2, Lex.Tok>}
  +m = Bool.pick(Nat, Paths.is_law_file(path), 0n, L1.prefix_count(T.sig(ts)))
  Equal.trans(Nat, List.length(&2, F.Finding, Prefix.check(Src.Src{path, text, ts, tree, bound, items})), m, 0n,
    L1.prefix_counts(path, text, ts, tree, bound, items),
    (%Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {Bool.pick(Nat, _, 0n, L1.prefix_count(T.sig(ts)))
      == 0n : Nat}; prefix.none_b(D1.prefix_fits(k, lit), f)))

def Laws.prefix_skips_drop_take_first(path, e, s, n, k, lit, l, c, f, text, tree, bound, items):
  +ts = {[Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TDotted{}, "String.drop", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TNum{}, n, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
    Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, k, l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]
    : List<&2, Lex.Tok>}
  +m = Bool.pick(Nat, Paths.is_law_file(path), 0n, L1.prefix_count(T.sig(ts)))
  Equal.trans(Nat, List.length(&2, F.Finding, Prefix.check(Src.Src{path, text, ts, tree, bound, items})), m, 0n,
    L1.prefix_counts(path, text, ts, tree, bound, items),
    (%Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {Bool.pick(Nat, _, 0n, L1.prefix_count(T.sig(ts)))
      == 0n : Nat}; prefix.none_a(D1.prefix_fits(k, lit), f)))

def Laws.prefix_skips_drop_literal_first(path, e, s, n, k, lit, l, c, f, text, tree, bound, items):
  +ts = {[Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TDotted{}, "String.drop", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TNum{}, n, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
    Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, k, l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]
    : List<&2, Lex.Tok>}
  +m = Bool.pick(Nat, Paths.is_law_file(path), 0n, L1.prefix_count(T.sig(ts)))
  Equal.trans(Nat, List.length(&2, F.Finding, Prefix.check(Src.Src{path, text, ts, tree, bound, items})), m, 0n,
    L1.prefix_counts(path, text, ts, tree, bound, items),
    (%Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {Bool.pick(Nat, _, 0n, L1.prefix_count(T.sig(ts)))
      == 0n : Nat}; prefix.none_b(D1.prefix_fits(k, lit), f)))
