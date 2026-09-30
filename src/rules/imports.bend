# src/rules/imports: paths and relative imports, as the project rules see
# them. A path is normalized (no `./`, `..` applied), an import resolves
# against the importing file's directory, and a file's closure is every file
# the linter read that it reaches by relative imports (`import ./m.bend as M`,
# `import ../x/y.bend as Y`). Imports of files that were not read are dropped:
# nothing is known of them.
import Base
import ../syntax/outline.bend as Outline
import ../lazy/lazy.bend as Lazy

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
  Bool.pick(String, Nat.is_eq(List.length(&2, String, segs), 0n), "", String.join(segs, "/") ++ "/")

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
      +more = deps.spec(rest, pp)
      Bool.pick(List<&2, String>, String.eq(ep, pp), ds, more)

# the files of ds that were read and are not yet seen, each once: the spec
# fresh.fast is proven against (imp.fresh)
def fresh.spec(ds: List<&2, String>, +seen: List<&2, String>, +read: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = fresh.spec(rest, seen, read)
      +known = Bool.and(has(read, d), Bool.not(has(seen, d)))  # noqa: U013 the spec fresh.fast is proven against
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
      +found = fresh.spec(deps.spec(es, p), seen, read)  # noqa: U013 the spec walk is proven against
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

# the walk: `walk.spec`, step for step, through the lookups above
def walk(
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
      +found = fresh.fast(deps.first(es, p), seen, read)  # noqa: U013 one lookup per file reached, fuel-bound
      walk(f, List.append(&2, String, found, rest), List.append(&2, String, List.reverse(&2, String, found), seen), es,
        read)

# the closure of the file at from, a path normalized already, over the graph
def closure.go(es: List<&2, Edge>, +read: List<&2, String>, +fuel: Nat, +from: String) -> List<&2, String>:
  List.reverse(&2, String, walk(fuel, [from], [from], es, read))

# a file the trail's walk has queued, and the files it was reached through,
# itself first and the start last
type Step is Data:
  Step{at: String, back: List<&2, String>}

# each file queued, reached through back
def steps(ds: List<&2, String>, +back: List<&2, String>) -> List<&2, Step>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      Step{d, d <> back} <> steps(rest, back)

# the walk `walk` takes, breadth first, each queued file carrying how it was
# reached, until it takes the file at to: the files from the start to it, in
# order; none when the walk never takes it
def trail.go(
  fuel: Nat,
  todo: List<&2, Step>,
  +seen: List<&2, String>,
  +es: List<&2, Edge>,
  +read: List<&2, String>,
  +to: String
) -> List<&2, String>:
  match fuel todo:
    case 0n t:
      Nil{}
    case 1n+f Nil{}:
      Nil{}
    case 1n+f Con{Step{+at, +back}, rest}:
      +found = fresh.fast(deps.first(es, at), seen, read)  # noqa: U013 one lookup per file on the path
      Lazy.stop(List<&2, String>, String.eq(at, to), List.reverse(&2, String, back),
        _u => trail.go(f, List.append(&2, Step, rest, steps(found, back)),
          List.append(&2, String, List.reverse(&2, String, found), seen), es, read, to))

# a shortest chain of relative imports from the file at from to the file at
# to, both normalized: the files in order, from first and to last
def trail(es: List<&2, Edge>, +read: List<&2, String>, +fuel: Nat, +from: String, +to: String) -> List<&2, String>:
  trail.go(fuel, [Step{from, [from]}], [from], es, read, to)
