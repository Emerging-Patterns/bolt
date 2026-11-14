# proofs of laws/ScopeExemptionsFollowPaths.bend
import Base
import ../src/finding.bend as F
import ../src/rules/style/reach.bend as Reach
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/correctness/hole.bend as Hole
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/rules/style/doc.bend as Doc
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/tail.bend as Tail
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../src/rules/pedantic/strict.bend as Strict
import ../src/rules/pedantic/index.bend as Index
import ../src/rules/laws/closed.bend as Closed
import ../src/rules/suspicious/thunk.bend as Thunk
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/ScopeExemptionsFollowPaths.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.scope_digest_exempt(_path, _text, _toks, _tree, _bound, _items, _text2, _toks2, _tree2, _bound2, _items2):
  {==}

# two finding lists that are both empty are equal
law scope.same:
  for -a: List<&2, F.Finding>
  for -b: List<&2, F.Finding>
  for ea: {a == Nil{} : List<&2, F.Finding>}
  for eb: {b == Nil{} : List<&2, F.Finding>}
  {a == b : List<&2, F.Finding>}

def scope.same(a, b, ea, eb):
  Equal.trans(List<&2, F.Finding>, a, Nil{}, b, ea, Equal.sym(List<&2, F.Finding>, b, Nil{}, eb))

def Laws.scope_hole(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Hole.check(Src.Src{path, text, toks, tree, bound, items}),
    Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    L1.hole_exempt(path, text, toks, tree, bound, items, e),
    L1.hole_exempt(path, text2, toks2, tree2, bound2, items2, e))

def Laws.scope_doc(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Doc.check(Src.Src{path, text, toks, tree, bound, items}),
    Doc.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    L1.doc_exempt(path, text, toks, tree, bound, items, e),
    L1.doc_exempt(path, text2, toks2, tree2, bound2, items2, e))

def Laws.scope_reach(max, path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Reach.check(Src.Src{path, text, toks, tree, bound, items}, max),
    Reach.check(Src.Src{path, text2, toks2, tree2, bound2, items2}, max),
    L1.reach_exempt(max, path, text, toks, tree, bound, items, e),
    L1.reach_exempt(max, path, text2, toks2, tree2, bound2, items2, e))

# two empty heads onto equal tails make equal lists
law scope.con:
  for -x: List<&2, F.Finding>
  for -y: List<&2, F.Finding>
  for ex: {x == Nil{} : List<&2, F.Finding>}
  for ey: {y == Nil{} : List<&2, F.Finding>}
  for -xs: List<&2, List<&2, F.Finding>>
  for -ys: List<&2, List<&2, F.Finding>>
  for ih: {xs == ys : List<&2, List<&2, F.Finding>>}
  {x <> xs == y <> ys : List<&2, List<&2, F.Finding>>}

def scope.con(x, y, ex, ey, xs, ys, ih):
  sx = Equal.sym(List<&2, F.Finding>, x, Nil{}, ex)
  sy = Equal.sym(List<&2, F.Finding>, y, Nil{}, ey)
  %sx : {_ <> xs == y <> ys : List<&2, List<&2, F.Finding>>}
  %sy : {Nil{} <> xs == _ <> ys : List<&2, List<&2, F.Finding>>}
  %ih : {Nil{} <> xs == Nil{} <> _ : List<&2, List<&2, F.Finding>>}
  {==}

def Laws.scope_law_file(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  +s = {Src.Src{path, text, toks, tree, bound, items} : Src.Src}
  +t = {Src.Src{path, text2, toks2, tree2, bound2, items2} : Src.Src}
  scope.con(Pick.check(s), Pick.check(t),
    L1.pick_exempt(path, text, toks, tree, bound, items, e),
    L1.pick_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Tail.check(s), Concat.check(s), Eager.check(s), Rewalk.check(s), Strict.check(s), Index.check(s), Thunk.check(s)],
    [Tail.check(t), Concat.check(t), Eager.check(t), Rewalk.check(t), Strict.check(t), Index.check(t), Thunk.check(t)],
  scope.con(Tail.check(s), Tail.check(t),
    L1.tail_exempt(path, text, toks, tree, bound, items, e),
    L1.tail_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Concat.check(s), Eager.check(s), Rewalk.check(s), Strict.check(s), Index.check(s), Thunk.check(s)],
    [Concat.check(t), Eager.check(t), Rewalk.check(t), Strict.check(t), Index.check(t), Thunk.check(t)],
  scope.con(Concat.check(s), Concat.check(t),
    L1.concat_exempt(path, text, toks, tree, bound, items, e),
    L1.concat_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Eager.check(s), Rewalk.check(s), Strict.check(s), Index.check(s), Thunk.check(s)],
    [Eager.check(t), Rewalk.check(t), Strict.check(t), Index.check(t), Thunk.check(t)],
  scope.con(Eager.check(s), Eager.check(t),
    L1.eager_exempt(path, text, toks, tree, bound, items, e),
    L1.eager_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Rewalk.check(s), Strict.check(s), Index.check(s), Thunk.check(s)],
    [Rewalk.check(t), Strict.check(t), Index.check(t), Thunk.check(t)],
  scope.con(Rewalk.check(s), Rewalk.check(t),
    L1.rewalk_exempt(path, text, toks, tree, bound, items, e),
    L1.rewalk_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Strict.check(s), Index.check(s), Thunk.check(s)],
    [Strict.check(t), Index.check(t), Thunk.check(t)],
  scope.con(Strict.check(s), Strict.check(t),
    L1.strict_exempt(path, text, toks, tree, bound, items, e),
    L1.strict_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Index.check(s), Thunk.check(s)],
    [Index.check(t), Thunk.check(t)],
  scope.con(Index.check(s), Index.check(t),
    L1.index_exempt(path, text, toks, tree, bound, items, e),
    L1.index_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Thunk.check(s)],
    [Thunk.check(t)],
  scope.con(Thunk.check(s), Thunk.check(t),
    L1.thunk_exempt(path, text, toks, tree, bound, items, e),
    L1.thunk_exempt(path, text2, toks2, tree2, bound2, items2, e),
    Nil{},
    Nil{},
  {==}))))))))

# closed reports nothing outside a LAWS.bend
law scope.closed:
  for +path: String
  for tree: Tree.Node
  for e: {Paths.is_laws(path) == False{} : Bool}
  {Lazy.stop(List<&2, F.Finding>, Bool.not(Paths.is_laws(path)), [], _u => Closed.check.go(tree, path))
    == Nil{} : List<&2, F.Finding>}

def scope.closed(path, tree, e):
  s = Equal.sym(Bool, Paths.is_laws(path), False{}, e)
  %s : {Lazy.stop(List<&2, F.Finding>, Bool.not(_), [], _u => Closed.check.go(tree, path))
    == Nil{} : List<&2, F.Finding>}
  {==}

def Laws.scope_closed(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Closed.check(Src.Src{path, text, toks, tree, bound, items}),
    Closed.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    scope.closed(path, tree, e), scope.closed(path, tree2, e))
