# rule unused: a name bound by a let, a do-bind, a lambda, or as a parameter
# is never used. Pattern binders are exempt: naming every field of
# `Tok{k, t, l, c}` reads better than `_`. So are names starting with `_`,
# erased parameters (`-x`), which exist to be unused, a law's `for` names
# (hypotheses the proof takes by position), and every parameter of a foreign
# def (one whose body starts with `import`), which its C and JS bodies read,
# however its header is wrapped.
import Base
import ../../src.bend as Src
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/bind.bend as Bind
import ../../syntax/tree.bend as Tree
import ../../syntax/lex.bend as Lex

# the lines of these tokens, onto acc
def lines(ts: List<&2, Lex.Tok>, acc: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      acc
    case Con{Lex.Tok{k, t, l, c}, rest}:
      l <> lines(rest, acc)

# every header line of the defs whose body is `import "./x.c"`, however the
# header is wrapped
def foreign(root: Tree.Node) -> List<&2, U32>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, Tree.NCons{Tree.Stmt{Tree.SImport{}, ik, ib}, more}}, rest}:
      lines(Tree.leaves(kids), foreign(rest))
    case Tree.NCons{other, rest}:
      foreign(rest)
    case other:
      Nil{}

# does a binder of this kind count? Erased and foreign parameters do not
def reportable(kk: Bind.BindKind, +note: String, +line: U32, +foreign_lines: List<&2, U32>) -> Bool:
  match kk:
    case Bind.KLocal{}:
      True{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, foreign_lines, line)))
    case other:
      False{}

# is the binder at (line, col) the target of any use?
def used(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, l, c, Bind.TLocal{+tl, +tc}}, rest}:
      Lazy.or_else(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), _u => used(rest, line, col))
    case Con{other, rest}:
      used(rest, line, col)

# a binder's kind, for the message
def what(kk: Bind.BindKind) -> String:
  match kk:
    case Bind.KParam{}:
      "Parameter"
    case other:
      "Local"

# a use's target, as the index holds it
type Cell is Data:
  Cell{line: U32, col: U32}

# the targets of the uses, as a binary trie on the low bits of each target's
# line, a leaf holding the cells that reach it. A hit in it is a use; a miss
# is checked against the uses themselves (seen), so the index only has to be
# sound, never complete, and a lookup is a walk down, not a scan of every use
type Hits is Data:
  HNone{}
  HLeaf{cells: List<&2, Cell>}
  HNode{lo: Hits, hi: Hits}

# how many bits of a line the index branches on
def depth() -> Nat:
  16n

# a line's way down the index: its low bits, lowest first
def path(dd: Nat, +key: U32) -> List<&2, Bool>:
  match dd:
    case 0n:
      Nil{}
    case 1n+p:
      U32.is_even(key) <> path(p, U32.shr(key))

# the cells at a leaf, none elsewhere
def hits.cells(hh: Hits) -> List<&2, Cell>:
  match hh:
    case HNone{}:
      Nil{}
    case HLeaf{cells}:
      cells
    case HNode{_lo, _hi}:
      Nil{}

# a node's low half, empty elsewhere
def hits.lo(hh: Hits) -> Hits:
  match hh:
    case HNone{}:
      HNone{}
    case HLeaf{_cells}:
      HNone{}
    case HNode{lo, _hi}:
      lo

# a node's high half, empty elsewhere
def hits.hi(hh: Hits) -> Hits:
  match hh:
    case HNone{}:
      HNone{}
    case HLeaf{_cells}:
      HNone{}
    case HNode{_lo, hi}:
      hi

# the half of a node a bit goes down, empty elsewhere
def hits.near(bb: Bool, hh: Hits) -> Hits:
  match bb:
    case True{}:
      hits.lo(hh)
    case False{}:
      hits.hi(hh)

# a node whose half down a bit is sub, and the other half far
def hits.join(bb: Bool, sub: Hits, far: Hits) -> Hits:
  match bb:
    case True{}:
      HNode{sub, far}
    case False{}:
      HNode{far, sub}

# the index with one more cell, down its path
def put(pp: List<&2, Bool>, +hh: Hits, +cell: Cell) -> Hits:
  match pp:
    case Nil{}:
      HLeaf{cell <> hits.cells(hh)}
    case Con{+bb, rest}:
      hits.join(bb, put(rest, hits.near(bb, hh), cell), hits.near(Bool.not(bb), hh))

# is the cell at (line, col) among these?
def hits.any(cs: List<&2, Cell>, +line: U32, +col: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{Cell{l, c}, rest}:
      Lazy.or_else(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), _u => hits.any(rest, line, col))

# is the cell at (line, col) at the end of a path through the index?
def find(pp: List<&2, Bool>, hh: Hits, +line: U32, +col: U32) -> Bool:
  match pp:
    case Nil{}:
      hits.any(hits.cells(hh), line, col)
    case Con{bb, rest}:
      find(rest, hits.near(bb, hh), line, col)

# a use's target into the index, when it is a binder of the file
def index.one(tg: Bind.Target, +hh: Hits) -> Hits:
  match tg:
    case Bind.TLocal{+tl, tc}:
      put(path(depth(), tl), hh, Cell{tl, tc})
    case Bind.TItem{_n}:
      hh
    case Bind.TQual{_a, _n}:
      hh
    case Bind.TFree{}:
      hh

# the index of every use's target
def index(uses: List<&2, Bind.Use>) -> Hits:
  match uses:
    case Nil{}:
      HNone{}
    case Con{Bind.Use{_n, _l, _c, tg}, rest}:
      index.one(tg, index(rest))

# is the binder at (line, col) the target of any use? The index answers a
# hit at once; only a miss reads the uses
def seen(hh: Hits, +uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  Lazy.or_else(find(path(depth(), line), hh, line, col), _u => used(uses, line, col))

def check.go(
  binds: List<&2, Bind.Bind>,
  +hh: Hits,
  +uses: List<&2, Bind.Use>,
  +fl: List<&2, U32>,
  +path: String
) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+name, +line, +col, +kind, note}, rest}:
      +more = check.go(rest, hh, uses, fl, path)
      +hit = Bool.and(reportable(kind, note, line, fl), Bool.not(String.starts_with(name, "_")))
      Bool.pick(List<&2, F.Finding>, Lazy.and_then(hit, _u => Bool.not(seen(hh, uses, line, col))),
        F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
          what(kind) ++ " " ++ name ++ " is never used."} <> more, more)

def check.on(bb: Bind.Bound, fl: List<&2, U32>, path: String) -> List<&2, F.Finding>:
  Bind.Bound{binds, +uses, scopes} = bb
  check.go(binds, index(uses), uses, fl, path)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.on(bound, foreign(tree), path)
