# walk/fake: a canned tree: a source file at the top and one two levels down,
# beside directories the walk must not descend into.
import Base
import ./service.bend as S

# the entries of the one directory this tree knows, else nothing
def at(+dir: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(dir, "."), ["bolt/", "b.bend", "node_modules/", ".gate/", "notes.md"],
    Bool.pick(List<&2, String>, String.eq(dir, "./bolt"), ["lsp/", "a.bend"],
      Bool.pick(List<&2, String>, String.eq(dir, "./bolt/lsp"), ["run.bend"],
        Bool.pick(List<&2, String>, String.eq(dir, "./node_modules"), ["dep.bend"],
          Bool.pick(List<&2, String>, String.eq(dir, "./.gate"), ["built.bend"], [])))))

# a directory's entries, from the canned tree
def entries(dir: String) -> IO(List<&2, String>):
  IO.pure(List<&2, String>, at(dir))

# the canned tree
def new() -> S.Walk:
  S.Walk{entries}
