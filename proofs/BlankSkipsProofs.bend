# proofs of laws/BlankSkipsProofs.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/blank.bend as Blank
import ../laws/defs/BlankTests.bend as D1
import ../laws/defs/EmptyTests.bend as D2
import ../laws/BlankSkipsProofs.bend as Laws

def Laws.blank_skips_in_law(path, e, xx, ll, cc, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D2.empty.in_law(D1.blank.second(xx, "\"\"", ll, cc), ll, cc)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_in_untyped_def(path, e, xx, ll, cc, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D2.empty.in_untyped(D1.blank.second(xx, "\"\"", ll, cc), ll, cc)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_in_proof_def(path, e, xx, ll, cc, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D2.empty.in_proof(D1.blank.second(xx, "\"\"", ll, cc), ll, cc)), path, False{}))) == 0n : Nat}
  {==}
