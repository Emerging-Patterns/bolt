# proofs of laws/EmptyReportsKeptTest.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/defs/EmptyTests.bend as D1
import ../laws/EmptyReportsKeptTest.bend as Laws
import ./lemmas/UnsafeStringCompare.bend as M1

# what follows the test in the kept sources: `,`, x and `)`
def empty.after(+x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]

# x is read in what follows the test
law empty.kept_x:
  for +x: String
  for +l: U32
  for +c: U32
  {Empty.kept(empty.after(x, l, c), x, 0n, False{}, True{}) == True{} : Bool}

def empty.kept_x(x, l, c):
  %Equal.sym(Bool, String.eq(x, x), True{}, M1.unsafe.srefl(x)) :
    {Empty.kept([Lex.Tok{Lex.TClose{}, ")", l, c}], x, 0n, _, True{}) == True{} : Bool}
  {==}

def Laws.empty_reports_list_kept(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c)), path, False{}))) == 1n : Nat}
  %Equal.sym(Bool, Empty.kept(empty.after(x, l, c), x, 0n, False{}, True{}), True{}, empty.kept_x(x, l, c)) :
    {List.length(&2, F.Finding, Empty.hit(Empty.tail.go(_, Empty.FList{}, x, l, c), path, Nil{})) == 1n : Nat}
  {==}

def Laws.empty_reports_string_kept(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.kept(D1.empty.str_test(x, l, c), x, l, c)), path, False{}))) == 1n : Nat}
  %Equal.sym(Bool, Empty.kept(empty.after(x, l, c), x, 0n, False{}, True{}), True{}, empty.kept_x(x, l, c)) :
    {List.length(&2, F.Finding, Empty.hit(Empty.tail.go(_, Empty.FStr{}, x, l, c), path, Nil{})) == 1n : Nat}
  {==}

def Laws.empty_reports_in_typed_def(path, e, x, l, c, _text, _tree, _bound, _items):
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [],
    _u => Empty.walk(T.sig(D1.empty.in_typed(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c)), path,
    False{}))) == 1n : Nat}
  %Equal.sym(Bool, Empty.kept(empty.after(x, l, c), x, 0n, False{}, True{}), True{}, empty.kept_x(x, l, c)) :
    {List.length(&2, F.Finding, Empty.hit(Empty.tail.go(_, Empty.FList{}, x, l, c), path, Nil{})) == 1n : Nat}
  {==}
