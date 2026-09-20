# bolt/glob: what `bolt` lints when it is handed no files: every `.bend` file
# under a directory, sorted. A hidden name (`.git`, `.gate`, `.scratch`,
# `.claude`) and `node_modules` are not descended into. The walk keeps a queue
# of directories rather than nesting, as Bend has no mutual recursion: one def
# shrinks one argument, the fuel, which bounds how many directories are read.
import Base
import ./walk/service.bend as Walk

# a directory bolt never descends into
def skipped(+name: String) -> Bool:
  Bool.or(String.starts_with(name, "."), String.eq(name, "node_modules"))

# an entry's name without the "/" that marks it a directory
def bare(+name: String) -> String:
  String.take(name, Nat.sub(String.length(name), 1n))

# a name directly under a directory, as a path
def under(+dir: String, +name: String) -> String:
  dir ++ "/" ++ name

# the sub-directories of a listing worth descending into, as paths
def dirs(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, rest}:
      +more = dirs(rest, dir)
      +keep = Bool.and(String.ends_with(e, "/"), Bool.not(skipped(bare(e))))
      Bool.pick(List<&2, String>, keep, under(dir, bare(e)) <> more, more)

# the `.bend` files of a listing, as paths (a directory's name ends in "/")
def bends(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, rest}:
      +more = bends(rest, dir)
      Bool.pick(List<&2, String>, String.ends_with(e, ".bend"), under(dir, e) <> more, more)

# every `.bend` file under the directories still queued, the fuel bounding how
# many directories are read. What is found is put in front of what came before,
# not after it, so the walk stays linear; `find` sorts at the end regardless.
def walk(~w: Walk.Walk, fuel: Nat, queue: List<&2, String>, acc: List<&2, String>) -> IO(List<&2, String>):
  match fuel:
    case 0n:
      IO.pure(List<&2, String>, acc)
    case 1n+f:
      match queue:
        case Nil{}:
          IO.pure(List<&2, String>, acc)
        case Con{+dir, rest}:
          do IO<List<&2, String>>:
            +es : List<&2, String> <- Walk.entries(w, dir)
            walk(~w, f, List.append(&2, String, rest, dirs(es, dir)),
              List.append(&2, String, bends(es, dir), acc))

# every `.bend` file under a directory, sorted
def find(~w: Walk.Walk, dir: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    ps : List<&2, String> <- walk(~w, U32.to_nat(100000), [dir], [])
    return List.sort(~String, ~String.is_le, ps)
