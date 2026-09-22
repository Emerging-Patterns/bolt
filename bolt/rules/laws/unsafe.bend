# rule unsafe (project-wide): an `@unsafe def` that a LAWS.bend or PROOF.bend
# reaches by relative imports, over the files bolt read. The checker skips its
# termination check, prints "All terms check, but N defs rely on unsafe or
# foreign code:" (2.0.16: "with N unsafe annotation(s).") and exits 0, so a
# gate that only reads the exit status goes green on a proof that is not
# sound (a def that never returns proves anything). Recurse
# on a shrinking argument, or on a fuel, and drop the `@unsafe`; or keep the
# def out of what the laws import. An `@unsafe` def no law file reaches is
# not this rule's business. The rule reads each file's digest
# (bolt/rules/digest.bend), and takes every closure over one import graph.
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
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
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

# each unsafe def as a finding, reached from the law file
def report(us: List<&2, Digest.Unsafe>, +origin: String, +path: String) -> List<&2, F.Finding>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Digest.Unsafe{n, l, c}, rest}:
      F.Finding{path, l, c, 7, "unsafe", "@unsafe def " ++ n ++ " is reached from " ++ origin
        ++ ": the checker only warns there and exits 0; recurse on a shrinking argument or fuel"} <> report(rest, origin, path)

# the unsafe defs of a file, when a law file reaches it
def found(mm: Maybe<&2, String>, us: List<&2, Digest.Unsafe>, path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{origin}:
      report(us, origin, path)

def check.go(ds: List<&2, Digest.Digest>, +rs: List<&2, Reach>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
      List.append(&2, F.Finding, found(reacher(rs, norm), unsafes, path), check.go(rest, rs))

# the rule, over every file the linter read
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  +es = Digest.edges(ds)
  check.go(ds, reaches(ds, es, Imports.paths(es), List.length(&2, Digest.Digest, ds)))
