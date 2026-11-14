# proofs of laws/ScopeLawsGovernPackage.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/finding.bend as F
import ../src/rules/digest.bend as Digest
import ../src/rules/laws/law.bend as Law
import ../laws/ScopeLawsGovernPackage.bend as Laws

# Under law (laws/ScopeLawsGovernPackage.bend). The coverage rule turns on at the first LAWS.bend
# directory it finds and then walks every file; the laws say which files it
# grades. One lemma for the walk over the files, one for the switch.

# one file onto the rule's walk: skipped when exempt, graded otherwise
law scope3.go.step:
  for exempt: Bool
  for +tops: List<&2, Digest.Top>
  for +cl: List<&2, String>
  for +norm: String
  for +path: String
  for -more: List<&2, F.Finding>
  for -spec: List<&2, F.Finding>
  for ih: {more == spec : List<&2, F.Finding>}
  {Lazy.stop(List<&2, F.Finding>, exempt, more,
      _u => List.append(&2, F.Finding, Law.gaps(tops, cl, norm, path), more))
    == List.append(&2, F.Finding, Laws.graded_file(exempt, tops, cl, norm, path), spec) : List<&2, F.Finding>}

def scope3.go.step(exempt, tops, cl, norm, path, more, spec, ih):
  match exempt:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        r => List.append(&2, F.Finding, Law.gaps(tops, cl, norm, path), r),
        more, spec, ih)

# the rule's walk over the files grades every file under law
law scope3.go:
  for ds: List<&2, Digest.Digest>
  for +cl: List<&2, String>
  {Law.check.go(ds, cl) == Laws.under_law(ds, cl) : List<&2, F.Finding>}

def scope3.go(ds, cl):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, _dir, _is_laws, _is_law_file, exempt, +tops, _says, _deps, _laws, _links},
      +rest}:
      scope3.go.step(exempt, tops, cl, norm, path, Law.check.go(rest, cl), Laws.under_law(rest, cl),
        scope3.go(rest, cl))

# one file onto the law directories: the rule is on exactly when some file
# so far is a LAWS.bend
law scope3.first.step:
  for is_laws: Bool
  for +ds: List<&2, Digest.Digest>
  for +dir: String
  for +dirs: List<&2, String>
  for -on: Bool
  for ih: {Law.check.first(ds, dirs) == Laws.coverage_of(on, ds, Law.reached(Law.graph(ds))) : List<&2, F.Finding>}
  {Law.check.first(ds, Bool.pick(List<&2, String>, is_laws, dir <> dirs, dirs))
    == Laws.coverage_of(Bool.or(is_laws, on), ds, Law.reached(Law.graph(ds))) : List<&2, F.Finding>}

def scope3.first.step(is_laws, ds, _dir, _dirs, _on, ih):
  match is_laws:
    case True{}:
      scope3.go(ds, Law.reached(Law.graph(ds)))
    case False{}:
      ih

# the rule is on over the files exactly when one of them is a LAWS.bend
law scope3.first:
  for ds: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {Law.check.first(all, Law.law_dirs(ds)) == Laws.coverage_of(Laws.has_laws(ds), all, Law.reached(Law.graph(all)))
    : List<&2, F.Finding>}

def scope3.first(ds, all):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{_path, _norm, +dir, is_laws, _is_law_file, _exempt, _tops, _says, _deps, _laws, _links},
      +rest}:
      scope3.first.step(is_laws, all, dir, Law.law_dirs(rest), Laws.has_laws(rest), scope3.first(rest, all))

def Laws.under_law_all(ds):
  scope3.first(ds, ds)
