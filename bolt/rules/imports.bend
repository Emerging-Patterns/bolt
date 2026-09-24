# bolt/rules/imports: paths and relative imports, as the project rules see
# them. A path is normalized (no `./`, `..` applied), an import resolves
# against the importing file's directory, and a file's closure is every file
# the linter read that it reaches by relative imports (`import ./m.bend as M`,
# `import ../x/y.bend as Y`). Imports of files that were not read are dropped:
# nothing is known of them.
import Base
import ../../syntax/outline.bend as Outline
import ../../lazy/lazy.bend as Lazy

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

# a path's directory, with its slash (`bolt/lsp/`; `` at the root)
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

# what the file at p imports (nothing when it was not read)
def deps_of(es: List<&2, Edge>, +pp: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edge{+ep, ds}, rest}:
      +more = deps_of(rest, pp)
      Bool.pick(List<&2, String>, String.eq(ep, pp), ds, more)

# the files of ds that were read and are not yet seen, each once
def fresh(ds: List<&2, String>, +seen: List<&2, String>, +read: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = fresh(rest, seen, read)
      Bool.pick(List<&2, String>, Bool.and(Bool.and(has(read, d), Bool.not(has(seen, d))), Bool.not(has(more, d))),
        d <> more, more)

# the paths of the files
def paths(es: List<&2, Edge>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edge{p, ds}, rest}:
      p <> paths(rest)

# a worklist walk; each read file enters todo once, and a start that was
# not read imports nothing, so fuel as many as the files never runs out
# (bolt/rules/LAWS.bend unsafe_shut)
def reach(
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
      +found = fresh(deps_of(es, p), seen, read)
      reach(f, List.append(&2, String, found, rest), List.append(&2, String, List.reverse(&2, String, found), seen), es,
        read)

# the closure of the file at from, a path normalized already, over the graph
def closure.go(es: List<&2, Edge>, +read: List<&2, String>, +fuel: Nat, +from: String) -> List<&2, String>:
  List.reverse(&2, String, reach(fuel, [from], [from], es, read))
