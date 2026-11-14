# proofs of laws/BlankReportsEmptyLiteralTest.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/blank.bend as Blank
import ../laws/defs/BlankTests.bend as D1
import ../laws/defs/EmptyTests.bend as D2
import ../laws/BlankReportsEmptyLiteralTest.bend as Laws

def Laws.blank_reports_second(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.second(x, "\"\"", l, c)), path, False{}))) == 1n : Nat}
  {==}

def Laws.blank_reports_first(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.first(x, l, c)), path, False{}))) == 1n : Nat}
  {==}

def Laws.blank_skips_call(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.deep(x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_reports_in_typed_def(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D2.empty.in_typed(D1.blank.second(x, "\"\"", l, c), l, c)), path, False{}))) == 1n : Nat}
  {==}

def Laws.blank_skips_other_literal(path, e, x, l, c, lit, ne, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.second(x, lit, l, c)), path, False{}))) == 0n : Nat}
  %Equal.sym(Bool, String.eq(lit, "\"\""), False{}, ne) :
    {List.length(&2, F.Finding, Blank.hit(Bool.pick(Maybe<&2, String>, _, Some{x}, None{}), path, l, c, Nil{}))
      == 0n : Nat}
  {==}

def Laws.blank_skips_inner(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.inner(x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_aliased(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.aliased(x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_number(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.number(x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_joined(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.joined(x, l, c)), path, False{}))) == 0n : Nat}
  {==}

def Laws.blank_skips_longer(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Blank.walk(T.sig(D1.blank.longer(x, l, c)), path, False{}))) == 0n : Nat}
  {==}
