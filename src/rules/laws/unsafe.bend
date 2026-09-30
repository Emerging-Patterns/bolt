# rule unsafe (project-wide): an `@unsafe def` or a foreign def (its body
# only `import "./x.c"` / `import "./x.js"` lines, what rule foreign reads)
# that a LAWS.bend or PROOF.bend reaches by relative imports, over the files
# bolt read. Since bend 2.0.32 a proof passes only when no def it loads,
# imports included, is `@unsafe` or foreign or names one that is: every def
# of every imported module counts, named by a law or not. Otherwise `bend`
# prints `SOME PROOFS FAIL`, then `Error: N defs rely on unsafe or foreign
# code:` and a `- name` list, and exits 1 (2.0.34; before 2.0.32 it printed
# "All terms check, but ..." and exited 0). So the gate is red, and the
# message names the defs that lean on the effect, not the import that
# brought it in: this rule names that path, law file first. `@unsafe` skips
# the termination check (a def that never returns proves anything): recurse
# on a shrinking argument or on fuel, and drop it. A foreign effect is fine
# in the program, never under a law: move it into a sibling module no law
# file imports, and hand the laws' code the effect as a service record
# (AGENTS.md; snap, ezhttp, bolt and ez were restructured that way). A def no
# law file reaches is not this rule's business. Hash imports (`import
# 0x.../path`, resolved through BEND_LIB) are not followed: bolt reads only
# the files of the run. The rule reads each file's digest
# (src/rules/digest.bend), and takes every closure over one import graph.
import Base
import ../../finding.bend as F
import ../digest.bend as Digest
import ../imports.bend as Imports

# a law file and what it reaches
type Reach is Data:
  Reach{origin: String, files: List<&2, String>}

# every LAWS.bend and PROOF.bend with its closure over the graph
def reaches(
  ds: List<&2, Digest.Digest>,
  +es: List<&2, Imports.Edge>,
  +read: List<&2, String>,
  +fuel: Nat
) -> List<&2, Reach>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = reaches(rest, es, read, fuel)
      Bool.pick(List<&2, Reach>, is_law_file, Reach{path, Imports.closure.go(es, read, fuel, norm)} <> more, more)

# the first law file that reaches the path
def reacher(rs: List<&2, Reach>, +pp: String) -> Maybe<&2, String>:
  match rs:
    case Nil{}:
      None{}
    case Con{Reach{origin, ps}, rest}:
      +more = reacher(rest, pp)
      Bool.pick(Maybe<&2, String>, Imports.has(ps, pp), Some{origin}, more)

# what a def reached from a law file along the import path via is, and what
# to do about it
def say(foreign: Bool, +name: String, +origin: String, +via: String) -> String:
  match foreign:
    case True{}:
      "foreign def " ++ name ++ " is reachable from " ++ origin ++ " (" ++ via
        ++ "), so bend fails that proof: SOME PROOFS FAIL, defs rely on unsafe or foreign code; move the effect into a sibling module no law file imports, and pass it in as a service."
    case False{}:
      "@unsafe def " ++ name ++ " is reachable from " ++ origin ++ " (" ++ via
        ++ "), so bend fails that proof: SOME PROOFS FAIL, defs rely on unsafe or foreign code; recurse on a shrinking argument or on fuel and drop @unsafe, or move it into a sibling module no law file imports."

# each unsafe or foreign def as a finding, at its `@unsafe` or its `def`,
# reached from the law file along the import path via
def report(us: List<&2, Digest.Unsafe>, +origin: String, +via: String, +path: String) -> List<&2, F.Finding>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Digest.Unsafe{n, l, c, +fo}, rest}:
      F.Finding{path, l, c, Bool.pick(U32, fo, 3, 7), "unsafe", say(fo, n, origin, via)} <> report(rest, origin, via, path)

# the import path from the file at from to the file at to, both normalized,
# as `a -> b -> c`
def via(es: List<&2, Imports.Edge>, +read: List<&2, String>, +fuel: Nat, +from: String, +to: String) -> String:
  String.join(Imports.trail(es, read, fuel, from, to), " -> ")

# the unsafe and foreign defs of the file at norm, reached from the law file
# at origin: the import path is looked for only when there is one
def found.some(
  us: List<&2, Digest.Unsafe>,
  +origin: String,
  +path: String,
  +norm: String,
  +es: List<&2, Imports.Edge>,
  +read: List<&2, String>,
  +fuel: Nat
) -> List<&2, F.Finding>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, rest}:
      report(u <> rest, origin, via(es, read, fuel, Imports.norm(origin), norm), path)

# the unsafe and foreign defs of a file, when a law file reaches it
def found(
  mm: Maybe<&2, String>,
  us: List<&2, Digest.Unsafe>,
  +path: String,
  +norm: String,
  +es: List<&2, Imports.Edge>,
  +read: List<&2, String>,
  +fuel: Nat
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{origin}:
      found.some(us, origin, path, norm, es, read, fuel)

def check.go(
  ds: List<&2, Digest.Digest>,
  +rs: List<&2, Reach>,
  +es: List<&2, Imports.Edge>,
  +read: List<&2, String>,
  +fuel: Nat
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      List.append(&2, F.Finding, found(reacher(rs, norm), unsafes, path, norm, es, read, fuel),
        check.go(rest, rs, es, read, fuel))

# the rule, over every file the linter read
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  +es = Digest.edges(ds)
  +read = Imports.paths(es)
  +fuel = List.length(&2, Digest.Digest, ds)
  check.go(ds, reaches(ds, es, read, fuel), es, read, fuel)
