# rule unused: a name bound by a let, a do-bind, a lambda, or as a parameter
# is never used. A name read anywhere is a use, in a dependent arrow's types
# too (`@+x: U32 -> S` reads `S`). Pattern binders are exempt: naming every
# field of `Tok{k, t, l, c}` reads better than `_`. So are names starting
# with `_`, erased parameters (`-x`), which exist to be unused, a law's `for`
# names (hypotheses the proof takes by position), and every parameter of a
# foreign def, which its C and JS bodies read: one whose body's first
# statement is `import`, wherever its header's `->` and return type fall (the
# body is what is under the whole header, Calls.under, so `-> IO(T):` on the
# line after `def f(..) ->` is no part of it).
import Base
import ../../src.bend as Src
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/bind.bend as Bind
import ../../syntax/tree.bend as Tree
import ../../syntax/lex.bend as Lex
import ../calls.bend as Calls

# the lines of these tokens, onto acc
def lines(ts: List<&2, Lex.Tok>, acc: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      acc
    case Con{Lex.Tok{k, t, l, c}, rest}:
      l <> lines(rest, acc)

# is the statement an import?
def foreign.first(sk: Tree.StmtKind) -> Bool:
  match sk:
    case Tree.SImport{}:
      True{}
    case other:
      False{}

# does a body open with an import?
def foreign.opens(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{sk, _kids, _b}, _rest}:
      foreign.first(sk)
    case other:
      False{}

# every header line of the defs whose body is `import "./x.c"`, wherever the
# header's `->` and return type fall
def foreign(root: Tree.Node) -> List<&2, U32>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      +more = foreign(rest)
      +own = lines(Tree.leaves(kids), more)
      Bool.pick(List<&2, U32>, foreign.opens(Calls.under(kids, body)), own, more)
    case Tree.NCons{other, rest}:
      foreign(rest)
    case other:
      Nil{}

# does a binder of this kind count? Erased and foreign parameters do not
def reportable(k: Bind.BindKind, +note: String, +line: U32, +foreign_lines: List<&2, U32>) -> Bool:
  match k:
    case Bind.KLocal{}:
      True{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, foreign_lines, line)))
    case other:
      False{}

# a binder's kind, for the message
def what(k: Bind.BindKind) -> String:
  match k:
    case Bind.KParam{}:
      "Parameter"
    case other:
      "Local"

# a use's target, as the index holds it
type Cell is Data:
  Cell{line: U32, col: U32}

# the targets of the uses, as a binary trie on the low bits of each target's
# line, a leaf holding the cells that reach it. It holds every use that
# resolves to a binder of the file and nothing else, so a lookup, a walk
# down to one leaf, answers for the uses themselves: a hit is a use and a
# miss is none (the proof of laws/UnusedReportsDeadBinders.bend). A miss
# used to be checked by a scan of every use, which made a file's unused
# binders times its uses: a 2.2 MB proof file spent 32 s there
type Hits is Data:
  HNone{}
  HLeaf{cells: List<&2, Cell>}
  HNode{lo: Hits, hi: Hits}

# how many bits of a line the index branches on
def depth() -> Nat:
  16n

# a line's way down the index: its low bits, lowest first
def path(d: Nat, +key: U32) -> List<&2, Bool>:
  match d:
    case 0n:
      Nil{}
    case 1n+p:
      U32.is_even(key) <> path(p, U32.shr(key))

# the cells at a leaf, none elsewhere
def hits.cells(h: Hits) -> List<&2, Cell>:
  match h:
    case HNone{}:
      Nil{}
    case HLeaf{cells}:
      cells
    case HNode{_lo, _hi}:
      Nil{}

# a node's low half, empty elsewhere
def hits.lo(h: Hits) -> Hits:
  match h:
    case HNone{}:
      HNone{}
    case HLeaf{_cells}:
      HNone{}
    case HNode{lo, _hi}:
      lo

# a node's high half, empty elsewhere
def hits.hi(h: Hits) -> Hits:
  match h:
    case HNone{}:
      HNone{}
    case HLeaf{_cells}:
      HNone{}
    case HNode{_lo, hi}:
      hi

# the half of a node a bit goes down, empty elsewhere
def hits.near(b: Bool, h: Hits) -> Hits:
  match b:
    case True{}:
      hits.lo(h)
    case False{}:
      hits.hi(h)

# a node whose half down a bit is sub, and the other half far
def hits.join(b: Bool, sub: Hits, far: Hits) -> Hits:
  match b:
    case True{}:
      HNode{sub, far}
    case False{}:
      HNode{far, sub}

# the index with one more cell, down its path
def put(p: List<&2, Bool>, +h: Hits, +cell: Cell) -> Hits:
  match p:
    case Nil{}:
      HLeaf{cell <> hits.cells(h)}
    case Con{+b, rest}:
      hits.join(b, put(rest, hits.near(b, h), cell), hits.near(Bool.not(b), h))

# is the cell at (line, col) among these?
def hits.any(cs: List<&2, Cell>, +line: U32, +col: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{Cell{l, c}, rest}:
      Lazy.or_else(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), _u => hits.any(rest, line, col))

# is the cell at (line, col) at the end of a path through the index?
def find(p: List<&2, Bool>, h: Hits, +line: U32, +col: U32) -> Bool:
  match p:
    case Nil{}:
      hits.any(hits.cells(h), line, col)
    case Con{b, rest}:
      find(rest, hits.near(b, h), line, col)

# a use's target into the index, when it is a binder of the file
def index.one(tg: Bind.Target, +h: Hits) -> Hits:
  match tg:
    case Bind.TLocal{+tl, tc}:
      put(path(depth(), tl), h, Cell{tl, tc})
    case Bind.TItem{_n}:
      h
    case Bind.TQual{_a, _n}:
      h
    case Bind.TFree{}:
      h

# the index of every use's target
def index(uses: List<&2, Bind.Use>) -> Hits:
  match uses:
    case Nil{}:
      HNone{}
    case Con{Bind.Use{_n, _l, _c, tg}, rest}:
      index.one(tg, index(rest))

# is the binder at (line, col) the target of any use? The index of the uses
# answers
def seen(h: Hits, +line: U32, +col: U32) -> Bool:
  find(path(depth(), line), h, line, col)

def check.go(binds: List<&2, Bind.Bind>, +h: Hits, +fl: List<&2, U32>, +path: String) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+name, +line, +col, +kind, note}, rest}:
      +more = check.go(rest, h, fl, path)
      +shown = reportable(kind, note, line, fl)
      +hit = Bool.and(shown, Bool.not(String.starts_with(name, "_")))
      Bool.pick(List<&2, F.Finding>, Lazy.and_then(hit, _u => Bool.not(seen(h, line, col))),
        F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
          what(kind) ++ " " ++ name ++ " is never used."} <> more, more)

def check.on(b: Bind.Bound, fl: List<&2, U32>, path: String) -> List<&2, F.Finding>:
  Bind.Bound{binds, uses, scopes} = b
  check.go(binds, index(uses), fl, path)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.on(bound, foreign(tree), path)
