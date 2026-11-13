# src/rules/imports: paths and relative imports, as the project rules see
# them. A path is normalized (no `./`, `..` applied), an import resolves
# against the importing file's directory, and a file's closure is every file
# the linter read that it reaches by relative imports (`import ./m.bend as M`,
# `import ../x/y.bend as Y`). Imports of files that were not read are dropped:
# nothing is known of them.
import Base
import ../syntax/outline.bend as Outline
import ../lazy/lazy.bend as Lazy
import ../syntax/bind.bend as Bind

# paths
# -----

# a segment onto the reversed path: `.` and empty are dropped, `..` pops
def norm.put(+ss: String, acc: List<&2, String>) -> List<&2, String>:
  match acc:
    case Con{+h, +t}:
      Bool.pick(List<&2, String>, String.eq(ss, ".."), t,
        Bool.pick(List<&2, String>, Bool.or(String.eq(ss, "."), String.is_empty(ss)), h <> t, ss <> (h <> t)))
    case Nil{}:
      Bool.pick(List<&2, String>, Bool.or(String.eq(ss, ".."), Bool.or(String.eq(ss, "."), String.is_empty(ss))),
        [], [ss])

def norm.go(segs: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{+s, rest}:
      norm.go(rest, norm.put(s, acc))

# a path without `./`, `../` and doubled slashes, so two spellings compare
def norm(path: String) -> String:
  String.join(norm.go(String.split(path, '/'), []), "/")

# the segments but the last
def init(segs: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      Nil{}
    case Con{h, Nil{}}:
      Nil{}
    case Con{h, t}:
      h <> init(t)

# a path's directory, with its slash (`src/lsp/`; `` at the root)
def dir_of(path: String) -> String:
  +segs = init(String.split(norm(path), '/'))
  Bool.pick(String, List.is_empty(&2, String, segs), "", String.join(segs, "/") ++ "/")

# a path imported from a file, normalized
def resolve(+from: String, rel: String) -> String:
  norm(dir_of(from) ++ rel)

# the import graph
# ----------------

# a file (normalized) and the files it imports relatively (normalized)
type Edge is Data:
  Edge{path: String, deps: List<&2, String>}

# the relative imports among a file's items, resolved against it
def targets(items: List<&2, Outline.Item>, +from: String) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IImport{}, name, line, sig, doc, +path}, rest}:
      +more = targets(rest, from)
      Lazy.stop(List<&2, String>, Bool.not(String.starts_with(path, ".")), more, _u => resolve(from, path) <> more)
    case Con{other, rest}:
      targets(rest, from)

# is the path among them?
def has(ps: List<&2, String>, +pp: String) -> Bool:
  List.contains(~String, ~String.eq, ps, pp)

# what the file at p imports (nothing when it was not read): the spec
# deps.first is proven against (src/rules/PROOF.bend imp.deps)
def deps.spec(es: List<&2, Edge>, +pp: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edge{+ep, ds}, rest}:
      +more = deps.spec(rest, pp)  # noqa: C003 the spec deps.first is proven against; only walk.spec runs it
      Bool.pick(List<&2, String>, String.eq(ep, pp), ds, more)

# the files of ds that were read and are not yet seen, each once: the spec
# fresh.fast is proven against (imp.fresh)
def fresh.spec(ds: List<&2, String>, +seen: List<&2, String>, +read: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = fresh.spec(rest, seen, read)
      +known = Bool.and(has(read, d), Bool.not(has(seen, d)))
      Bool.pick(List<&2, String>, Bool.and(known, Bool.not(has(more, d))), d <> more, more)

# the paths of the files
def paths(es: List<&2, Edge>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edge{p, ds}, rest}:
      p <> paths(rest)

# a worklist walk; each read file enters todo once, and a start that was
# not read imports nothing, so fuel as many as the files never runs out
# (src/rules/LAWS.bend unsafe_shut). The spec `walk` is proven against
# (imp.walk), and what the laws' proofs reason over
def walk.spec(
  fuel: Nat,
  todo: List<&2, String>,
  +seen: List<&2, String>,
  +es: List<&2, Edge>,
  +read: List<&2, String>
) -> List<&2, String>:
  match fuel todo:
    case 0n t:
      seen
    case 1n+f Nil{}:
      seen
    case 1n+f Con{p, rest}:
      +found = fresh.spec(deps.spec(es, p), seen, read)
      walk.spec(f, List.append(&2, String, found, rest), List.append(&2, String, List.reverse(&2, String, found), seen),
        es, read)

# `has`, stopping at the first hit
def seek(ps: List<&2, String>, +pp: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Lazy.or_else(String.eq(p, pp), _u => seek(rest, pp))

# `deps.spec`, stopping at the first file of that path
def deps.first(es: List<&2, Edge>, +pp: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edge{ep, ds}, rest}:
      Lazy.stop(List<&2, String>, String.eq(ep, pp), ds, _u => deps.first(rest, pp))

# `fresh.spec`, asking the short lists first and each only while the answer is
# open: a target already found or seen is never looked for among every file
def fresh.fast(ds: List<&2, String>, +seen: List<&2, String>, +read: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = fresh.fast(rest, seen, read)
      Bool.pick(List<&2, String>,
        Lazy.and_then(Bool.not(seek(more, d)), _u => Lazy.and_then(Bool.not(seek(seen, d)), _v => seek(read, d))),
        d <> more, more)

# The walk's indexes. Each step asks what a file imports, then whether each
# import was seen and was read, and scanning the edges, the files seen and
# the files read for each is the files squared: on a project of 4,062 files,
# 9.5 s of a 24 s run, three walks a role computation and two of those.
# So the edges are put in a trie on the low bits of each path's number, the
# binder index's shape (src/syntax/bind.bend), and the files seen and read
# in the binder's index itself, the seen ones put in as the walk finds them.
# A lookup off each is the scan (proofs/lemmas/WalkIndex.bend).
type EIx is Data:
  ENone{}
  ELeaf{es: List<&2, Edge>}
  ENode{lo: EIx, hi: EIx}

# the edges at a leaf, none elsewhere
def edges.ix.es(ix: EIx) -> List<&2, Edge>:
  match ix:
    case ENone{}:
      Nil{}
    case ELeaf{es}:
      es
    case ENode{_lo, _hi}:
      Nil{}

# the half a bit picks: an even bit the low half
def edges.ix.pick(bb: Bool, lo: EIx, hi: EIx) -> EIx:
  match bb:
    case True{}:
      lo
    case False{}:
      hi

# the half of a node a bit picks; none below anything else
def edges.ix.near(bb: Bool, ix: EIx) -> EIx:
  match ix:
    case ENode{lo, hi}:
      edges.ix.pick(bb, lo, hi)
    case other:
      ENone{}

# a node from the half a bit picks and the other half
def edges.ix.join(bb: Bool, sub: EIx, far: EIx) -> EIx:
  match bb:
    case True{}:
      ENode{sub, far}
    case False{}:
      ENode{far, sub}

# an edge put at the front of the leaf its path's number leads to
def edges.ix.put(dd: Nat, +kk: U32, +ix: EIx, ee: Edge) -> EIx:
  match dd:
    case 0n:
      ELeaf{ee <> edges.ix.es(ix)}
    case 1n+p:
      edges.ix.join(U32.is_even(kk), edges.ix.put(p, U32.shr(kk), edges.ix.near(U32.is_even(kk), ix), ee),
        edges.ix.near(Bool.not(U32.is_even(kk)), ix))

# the edges at the leaf a number's low bits lead to
def edges.ix.at(dd: Nat, +kk: U32, ix: EIx) -> List<&2, Edge>:
  match dd:
    case 0n:
      edges.ix.es(ix)
    case 1n+p:
      edges.ix.at(p, U32.shr(kk), edges.ix.near(U32.is_even(kk), ix))

# the index of these edges, each leaf in their order
def edges.ix.of(es: List<&2, Edge>) -> EIx:
  match es:
    case Nil{}:
      ENone{}
    case Con{Edge{+p, ds}, rest}:
      edges.ix.put(Bind.index.depth(), Bind.key(p), edges.ix.of(rest), Edge{p, ds})

# what the file at p imports, read off the index: deps.first's
def deps.ix(ex: EIx, +pp: String) -> List<&2, String>:
  deps.first(edges.ix.at(Bind.index.depth(), Bind.key(pp), ex), pp)

# these paths put in an index, the first nearest the top: the index of
# them followed by the ones it held
def seen.onto(xs: List<&2, String>, ix: Bind.Index) -> Bind.Index:
  match xs:
    case Nil{}:
      ix
    case Con{+x, rest}:
      Bind.index.put(Bind.index.depth(), Bind.key(x), seen.onto(rest, ix), x)

# `fresh.fast`, the files seen and read asked of their indexes
def fresh.ix(ds: List<&2, String>, +sx: Bind.Index, +rx: Bind.Index) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = fresh.ix(rest, sx, rx)
      Bool.pick(List<&2, String>,
        Lazy.and_then(Bool.not(seek(more, d)), _u => Lazy.and_then(Bool.not(Bind.indexed(sx, d)),
          _v => Bind.indexed(rx, d))),
        d <> more, more)

# `walk.spec`, step for step, through the indexes: sx the files seen, ex the
# edges, rx the files read
def walk.ix(
  fuel: Nat,
  todo: List<&2, String>,
  +seen: List<&2, String>,
  +sx: Bind.Index,
  +ex: EIx,
  +rx: Bind.Index
) -> List<&2, String>:
  match fuel todo:
    case 0n t:
      seen
    case 1n+f Nil{}:
      seen
    case 1n+f Con{+p, rest}:
      +found = fresh.ix(deps.ix(ex, p), sx, rx)
      walk.ix(f, List.append(&2, String, found, rest), List.append(&2, String, List.reverse(&2, String, found), seen),
        seen.onto(List.reverse(&2, String, found), sx), ex, rx)

# the walk: `walk.spec`, through the indexes above
def walk(
  fuel: Nat,
  todo: List<&2, String>,
  +seen: List<&2, String>,
  +es: List<&2, Edge>,
  +read: List<&2, String>
) -> List<&2, String>:
  walk.ix(fuel, todo, seen, Bind.index(seen), edges.ix.of(es), Bind.index(read))

# the closure of the file at from, a path normalized already, over the graph
def closure.go(es: List<&2, Edge>, +read: List<&2, String>, +fuel: Nat, +from: String) -> List<&2, String>:
  List.reverse(&2, String, walk(fuel, [from], [from], es, read))
