# definitions the laws share
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/rules/digest.bend as Digest
import ../../src/rules/imports.bend as Imports

# a token's columns: a string literal two, a `#|` comment none, a comment
# otherwise at its full width, and any other token its length
def share(kk: Lex.TokKind, +tt: String) -> U32:
  match kk:
    case Lex.TStr{}:
      2
    case Lex.TComment{}:
      Bool.pick(U32, String.starts_with(tt, "#|"), 0, U32.from_nat(String.length(tt)))
    case other:
      U32.from_nat(String.length(tt))

# the count more, one higher when a line is over 120 columns wide
def over(+width: U32, +more: Nat) -> Nat:
  Bool.pick(Nat, U32.is_gt(width, 120), 1n+more, more)

# Reach (laws/ImportReachIsClosed.bend), over every list of digests, as
# coverage's laws are. A digest records a file's relative imports
# (normalized, `deps`); the import graph is theirs, and the closure a file
# reaches over it is Imports.closure.go's, the walk every project rule
# shares.

# every file of the digests the file at from reaches by relative imports,
# itself first, as the closure walk takes it
def unsafe.closure(+all: List<&2, Digest.Digest>, from: String) -> List<&2, String>:
  Imports.closure.go(Digest.edges(all), Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all), from)

# unsafe (laws/UnsafeReportsReachableForeignDefs.bend), the reach. unsafe_reports reads what a law file
# reaches as unsafe.closure, the import walk the rule runs. These laws pin
# that walk to a spec written apart from it: the files in the run are the
# digests' paths, a file imports what its digest records, and what a file
# reaches is the least list that holds it and is shut: every file in the run
# that one of its files imports is in it. The walk counts down a fuel of one
# per digest; unsafe_shut says it never runs out.

# what the file at pp imports relatively, as the first digest of that path
# records it; nothing when no digest has the path
def unsafe.imports(ds: List<&2, Digest.Digest>, +pp: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, rest}:
      +more = unsafe.imports(rest, pp)
      Bool.pick(List<&2, String>, String.eq(norm, pp), deps, more)

# is the file at pp in the run: does a digest have that path?
def unsafe.read(ds: List<&2, Digest.Digest>, +pp: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, rest}:
      +more = unsafe.read(rest, pp)
      Bool.or(String.eq(norm, pp), more)

# every path of xs that is in the run is in ss
def unsafe.held(+ds: List<&2, Digest.Digest>, +ss: List<&2, String>, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      +more = unsafe.held(ds, ss, rest)
      Bool.and(Bool.or(Bool.not(unsafe.read(ds, x)), Imports.has(ss, x)), more)

# ss is shut over ps: every file in the run that a file of ps imports is in ss
def unsafe.shut(+ds: List<&2, Digest.Digest>, +ss: List<&2, String>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, rest}:
      +more = unsafe.shut(ds, ss, rest)
      Bool.and(unsafe.held(ds, ss, unsafe.imports(ds, p)), more)
