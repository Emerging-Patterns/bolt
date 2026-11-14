# rule spare (project): an import the file never names, of a file that is
# imported for its names alone. Reported: in a file that is neither a law
# file nor a proof file, an import of a file by a relative path under an
# alias (`import ./ops.bend as O`) when no dotted name of the file outside
# its import lines starts with the alias and a dot (`O.add`), the file does
# name the alias of another import of its own, the imported file was read
# in the run, and neither it nor any file it reaches by relative imports
# loads. One finding, on the import's line.
#
# A file loads when it states a law, holds a def that is a proof, or holds
# a foreign def (rules/links.bend). `bend` checks a law and a proof with
# whatever imports their file, and links a foreign def only when the entry
# reaches its file, so an import of such a file is made for what it does,
# whatever its alias: a module that imports its own proofs, a check that
# imports the entry to keep the native effects registered. Deleting one of
# those would silence the finding and drop a check, so it is never
# reported.
#
# A file that names none of its imports is left alone too: it loads them
# (an entry that lists what a package publishes, a harness, a file that
# exists to type-check a library). So is an import with no alias
# (`import Base`), one of a hub package (its path is not relative: nothing
# is known of it), and one whose target the run did not read.
#
# The fix is to delete the import line: the file says it depends on a
# module it does not use, `bend` checks that module for nothing, and a
# published package carries it.
#
# It needs every file, so it runs in `bolt` over a tree and never in the
# editor; over files named on the line it sees only those, and reports an
# import only when its target is among them.
import Base
import ../../finding.bend as F
import ../../lazy/lazy.bend as Lazy
import ../digest.bend as Digest
import ../imports.bend as Imports
import ../links.bend as Links

# a path before the others when its file loads
def loaders.put(loads: Bool, norm: String, more: List<&2, String>) -> List<&2, String>:
  match loads:
    case True{}:
      norm <> more
    case False{}:
      more

# the normalized paths of the files that load, in order
def loaders(ds: List<&2, Digest.Digest>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{
      Digest.Digest{_path, norm, _dir, _is_laws, _is_law_file, _exempt, _tops, _says, _deps, _laws,
        Links.Links{loads, _spare}}, rest}:
      loaders.put(loads, norm, loaders(rest))

# is any of the paths among the loaders?
def any(ps: List<&2, String>, +ls: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Lazy.or_else(Imports.seek(ls, p), _u => any(rest, ls))

# what the file at a path reaches by relative imports among the files read,
# itself first: the walk `coverage` takes (laws/ImportReachIsClosed.bend)
def closure(+all: List<&2, Digest.Digest>, target: String) -> List<&2, String>:
  Imports.closure.go(Digest.edges(all), Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all), target)

# does importing the file at a path load something: is the file, or one it
# reaches by relative imports among the files read, a loader?
def reaches(all: List<&2, Digest.Digest>, ls: List<&2, String>, target: String) -> Bool:
  any(closure(all, target), ls)

# was the file at a path read in the run?
def read(all: List<&2, Digest.Digest>, target: String) -> Bool:
  Imports.seek(Imports.paths(Digest.edges(all)), target)

# is a spare import reported: its target was read, and importing it loads
# nothing?
def idle(+all: List<&2, Digest.Digest>, ls: List<&2, String>, +target: String) -> Bool:
  Lazy.and_then(read(all, target), _u => Bool.not(reaches(all, ls, target)))

# what a finding says
def say(alias: String) -> String:
  "Import " ++ alias ++ " is never named in this file; delete the import."

# the finding on the import's line, over the word `import`
def cite(alias: String, line: U32, path: String) -> F.Finding:
  F.Finding{path, line, 0, 6, "spare", say(alias)}

# a finding on the import when it is reported, before the rest
def found(hit: Bool, alias: String, line: U32, path: String, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match hit:
    case True{}:
      cite(alias, line, path) <> more
    case False{}:
      more

# a file's spare imports that are reported, in order, before the rest
def file(
  ss: List<&2, Links.Spare>,
  +path: String,
  +all: List<&2, Digest.Digest>,
  +ls: List<&2, String>,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      more
    case Con{Links.Spare{alias, target, line}, rest}:
      found(idle(all, ls, target), alias, line, path, file(rest, path, all, ls, more))

# every reported import of every file that is neither a law file nor a
# proof file, in order: all are the files of the run, ls those that load
def check.go(ds: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>, +ls: List<&2, String>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{
      Digest.Digest{path, _norm, _dir, _is_laws, is_law_file, _exempt, _tops, _says, _deps, _laws,
        Links.Links{_loads, spare}}, rest}:
      +more = check.go(rest, all, ls)
      Lazy.stop(List<&2, F.Finding>, is_law_file, more, _u => file(spare, path, all, ls, more))

# the rule
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  check.go(ds, ds, loaders(ds))
