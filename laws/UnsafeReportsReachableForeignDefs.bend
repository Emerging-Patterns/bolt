# An `@unsafe def` or a foreign def (a def whose body is only imports of `.c`
# or `.js` files) reachable by relative imports from a law file in the run is
# a finding, at the def, that names the first such law file and the import
# path from it to the def's file.
import Base
import ../src/finding.bend as F
import ../src/rules/digest.bend as Digest
import ../src/rules/laws/unsafe.bend as Unsafe
import ../src/rules/imports.bend as Imports
import ./defs/Unsafe.bend as D1

# the import path from the file at from to the file at to, over the digests,
# as the finding spells it: `a -> b -> c`
def unsafe.via(+all: List<&2, Digest.Digest>, +from: String, +to: String) -> String:
  String.join(Imports.trail(Digest.edges(all), Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all),
    from, to), " -> ")

# the path of the first law file among ls (a LAWS.bend or a PROOF.bend)
# whose closure over all holds the path pp
def unsafe.origin(ls: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>, +pp: String) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      None{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = unsafe.origin(rest, all, pp)
      Bool.pick(Maybe<&2, String>, Bool.and(is_law_file, Imports.has(D1.unsafe.closure(all, norm), pp)), Some{path},
          more)

# what the finding says of a foreign or an `@unsafe` def, reached from the
# law file at origin along the import path via
def unsafe.says(foreign: Bool, +name: String, +origin: String, +via: String) -> String:
  match foreign:
    case True{}:
      "foreign def " ++ name ++ " is reachable from " ++ origin ++ " (" ++ via
        ++ "), so bend fails that proof: SOME PROOFS FAIL, defs rely on unsafe or foreign code; move the effect into a sibling module no law file imports, and pass it in as a service."
    case False{}:
      "@unsafe def " ++ name ++ " is reachable from " ++ origin ++ " (" ++ via
        ++ "), so bend fails that proof: SOME PROOFS FAIL, defs rely on unsafe or foreign code; recurse on a shrinking argument or on fuel and drop @unsafe, or move it into a sibling module no law file imports."

# one finding for each def, at its `@` (7 wide) or, a foreign def, its
# header's start (3 wide), naming the law file and the import path
def unsafe.each(us: List<&2, Digest.Unsafe>, +origin: String, +via: String, +path: String) -> List<&2, F.Finding>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Digest.Unsafe{n, l, c, +fo}, rest}:
      F.Finding{path, l, c, Bool.pick(U32, fo, 3, 7), "unsafe", unsafe.says(fo, n, origin, via)}
        <> unsafe.each(rest, origin, via, path)

# a file's unsafe and foreign defs when a law file reaches it, else nothing;
# the path runs from that law file to the file at norm
def unsafe.at(
  mm: Maybe<&2, String>,
  us: List<&2, Digest.Unsafe>,
  +path: String,
  +norm: String,
  +all: List<&2, Digest.Digest>
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{+origin}:
      unsafe.each(us, origin, unsafe.via(all, Imports.norm(origin), norm), path)

# the findings of every file of fs, in order, against the law files of all
def unsafe.files(fs: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      List.append(&2, F.Finding, unsafe.at(unsafe.origin(all, all, norm), unsafes, path, norm, all),
        unsafe.files(rest, all))

# LAW: over every list of digests, unsafe reports exactly each `@unsafe def`
# and each foreign def of each file that the closure of some law file holds,
# in file order, and names the first such law file and the import path from
# it to the file
law unsafe_reports:
  for +ds: List<&2, Digest.Digest>
  {Unsafe.check(ds) == unsafe.files(ds, ds) : List<&2, F.Finding>}

# LAW: over every list of digests, what the file at from reaches holds it
law unsafe_from:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {Imports.has(D1.unsafe.closure(ds, from), from) == True{} : Bool}

# LAW: over every list of digests, what a file reaches is shut: every file in
# the run that one of its files imports is in it. So the walk's fuel never
# cuts it short
law unsafe_shut:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {D1.unsafe.shut(ds, D1.unsafe.closure(ds, from), D1.unsafe.closure(ds, from)) == True{} : Bool}

# LAW: and it is the least such list: every list that holds from and is shut
# holds each file it reaches, so it reaches only files a chain of relative
# imports through the run leads to
law unsafe_least:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for +ss: List<&2, String>
  for +pp: String
  for hf: {Imports.has(ss, from) == True{} : Bool}
  for hs: {D1.unsafe.shut(ds, ss, ss) == True{} : Bool}
  for hp: {Imports.has(D1.unsafe.closure(ds, from), pp) == True{} : Bool}
  {Imports.has(ss, pp) == True{} : Bool}
