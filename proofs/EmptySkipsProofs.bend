# proofs of laws/EmptySkipsProofs.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/defs/EmptyTests.bend as D1
import ../laws/EmptySkipsProofs.bend as Laws

def Laws.empty_skips_in_law(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.in_law(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c)), path,
    False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_in_untyped_def(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.in_untyped(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c)), path,
    False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_in_proof_def(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.in_proof(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c)), path,
    False{}))) == 0n : Nat}
  {==}
