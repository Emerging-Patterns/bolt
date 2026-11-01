# When a package's files include a LAWS.bend, every file of that package that
# is not exempt is under law; otherwise none is.
#
# also rests on: laws/PackagesScoped.bend
import Base
import ../src/finding.bend as F
import ../src/rules/digest.bend as Digest
import ../src/rules/laws/law.bend as Law

# Under law (laws/ScopeLawsGovernPackage.bend). The coverage rule (rules/laws/law.bend) grades a
# file's defs and types only when the file is under law. This law says, over
# the digests the planner hands the project rules, which files those are.

# whether some file of the run is a LAWS.bend
def has_laws(ds: List<&2, Digest.Digest>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{_path, _norm, _dir, is_laws, _is_law_file, _exempt, _tops, _says, _deps, _laws},
      rest}:
      Bool.or(is_laws, has_laws(rest))

# a file under law, graded against what the laws reach: nothing when it is
# exempt, otherwise every def and type of it that no law reaches
def graded_file(
  exempt: Bool,
  +tops: List<&2, Digest.Top>,
  +cl: List<&2, String>,
  +norm: String,
  path: String
) -> List<&2, F.Finding>:
  match exempt:
    case True{}:
      []
    case False{}:
      Law.gaps(tops, cl, norm, path)

# every file of the run put under law, each graded against what the laws
# reach, in order
def under_law(ds: List<&2, Digest.Digest>, +cl: List<&2, String>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      []
    case Con{Digest.Digest{path, norm, _dir, _is_laws, _is_law_file, exempt, tops, _says, _deps, _laws},
      rest}:
      List.append(&2, F.Finding, graded_file(exempt, tops, cl, norm, path), under_law(rest, cl))

# a run's coverage findings: every file under law when the run holds a
# LAWS.bend, none otherwise
def coverage_of(on: Bool, ds: List<&2, Digest.Digest>, cl: List<&2, String>) -> List<&2, F.Finding>:
  match on:
    case True{}:
      under_law(ds, cl)
    case False{}:
      []

# LAW: when a package's files include a LAWS.bend, every one of them that is
# not exempt is under law, graded against what every law of the package
# reaches (rules/laws/law.bend); otherwise none is
law under_law_all:
  for +ds: List<&2, Digest.Digest>
  {Law.check(ds) == coverage_of(has_laws(ds), ds, Law.reached(Law.graph(ds))) : List<&2, F.Finding>}
