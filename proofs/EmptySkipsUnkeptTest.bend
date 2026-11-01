# proofs of laws/EmptySkipsUnkeptTest.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/defs/EmptyTests.bend as D1
import ../laws/EmptySkipsUnkeptTest.bend as Laws

def Laws.empty_skips_list_dropped(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.dropped(D1.empty.list_test(x, l, c), l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_string_dropped(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.dropped(D1.empty.str_test(x, l, c), l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_list_before(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.before(D1.empty.list_test(x, l, c), x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_string_before(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.before(D1.empty.str_test(x, l, c), x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_list_bare(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.bare(D1.empty.list_test(x, l, c), x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.empty_skips_string_bare(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.bare(D1.empty.str_test(x, l, c), x, l, c)), path, False{}))) == 0n : Nat}
  {==}
