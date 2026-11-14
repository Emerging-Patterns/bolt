# nearest package root, package scoping and coverage of packages
import Base
import ../../src/lazy/lazy.bend as Lazy
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules
import ../../src/role.bend as Role
import ../../src/rules/digest.bend as Digest
import ../../src/rules/laws/law.bend as Law
import ../../src/rules/suspicious/spare.bend as Spare
import ../../laws/PackagesScoped.bend as L1
import ../../laws/ScopePackageRootsFound.bend as L2
import ../../laws/defs/ScopeWalkFiles.bend as D1

# Packages (laws/ScopePackageRootsFound.bend, laws/ScopeProjectRulesRunOnRoot.bend). The planner and the rules use the
# lazy forms, the spec the strict ones; each lemma below takes the Bool
# apart, as laws/LazyMatchesEagerCombinators.bend does.

# a lazy or is the strict or, its rest equal
law pk.or:
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(b, _u => x) == Bool.or(b, y) : Bool}

def pk.or(b, _x, _y, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a lazy stop is the strict pick, its rest equal
law pk.stop:
  for b: Bool
  for +u: String
  for -x: String
  for -y: String
  for ih: {x == y : String}
  {Lazy.stop(String, b, u, _u => x) == Bool.pick(String, b, u, y) : String}

def pk.stop(b, _u, _x, _y, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the rules' search of the roots is the spec's
law pk.listed:
  for rs: List<&2, String>
  for +d: String
  {Rules.has(rs, d) == D1.listed(rs, d) : Bool}

def pk.listed(rs, d):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +tl}:
      pk.or(String.eq(r, d), Rules.has(tl, d), D1.listed(tl, d), pk.listed(tl, d))

# the rules' nearest root is the spec's
law pk.owner:
  for us: List<&2, String>
  for +rs: List<&2, String>
  {Rules.owner.go(us, rs) == D1.nearest(us, rs) : String}

def pk.owner(us, rs):
  match us:
    case Nil{}:
      {==}
    case Con{+u, +tl}:
      a = pk.listed(rs, u)
      %a : {Lazy.stop(String, Rules.has(rs, u), u, _u => Rules.owner.go(tl, rs))
        == Bool.pick(String, _, u, D1.nearest(tl, rs)) : String}
      pk.stop(Rules.has(rs, u), u, Rules.owner.go(tl, rs), D1.nearest(tl, rs), pk.owner(tl, rs))

def L2.package_nearest(rs, dir):
  pk.owner(Rules.ups(dir), rs)

# the rules' files of a package are the spec's
law pk.members:
  for ds: List<&2, Digest.Digest>
  for +rs: List<&2, String>
  for +pkg: String
  {Rules.members(ds, rs, pkg) == D1.part(ds, rs, pkg) : List<&2, Digest.Digest>}

def pk.members(ds, rs, pkg):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, +dir, +is_laws, +is_law_file, +exempt, +tops, +says, +deps, +laws, +links},
      +tl}:
      a = L2.package_nearest(rs, dir)
      %a : {Bool.pick(List<&2, Digest.Digest>, String.eq(Rules.owner(rs, dir), pkg),
          Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links}
            <> Rules.members(tl, rs, pkg), Rules.members(tl, rs, pkg))
        == Bool.pick(List<&2, Digest.Digest>, String.eq(_, pkg),
          Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links}
            <> D1.part(tl, rs, pkg), D1.part(tl, rs, pkg))
        : List<&2, Digest.Digest>}
      e = pk.members(tl, rs, pkg)
      %e : {Bool.pick(List<&2, Digest.Digest>, String.eq(Rules.owner(rs, dir), pkg),
          Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links}
            <> Rules.members(tl, rs, pkg), Rules.members(tl, rs, pkg))
        == Bool.pick(List<&2, Digest.Digest>, String.eq(Rules.owner(rs, dir), pkg),
          Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links} <> _, _)
        : List<&2, Digest.Digest>}
      {==}

# the rules' coverage of the packages is the spec's
law pk.covers:
  for ps: List<&2, String>
  for +ds: List<&2, Digest.Digest>
  for +rs: List<&2, String>
  {Rules.covers(ps, ds, rs) == D1.covered(ps, ds, rs) : List<&2, F.Finding>}

def pk.covers(ps, ds, rs):
  match ps:
    case Nil{}:
      {==}
    case Con{+dir, +tl}:
      m = pk.members(ds, rs, dir)
      %m : {List.append(&2, F.Finding, Law.check(Rules.members(ds, rs, dir)), Rules.covers(tl, ds, rs))
        == List.append(&2, F.Finding, Law.check(_), D1.covered(tl, ds, rs)) : List<&2, F.Finding>}
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        xs => List.append(&2, F.Finding, Law.check(Rules.members(ds, rs, dir)), xs),
        Rules.covers(tl, ds, rs), D1.covered(tl, ds, rs), pk.covers(tl, ds, rs))

def L1.packages_scoped(srcs, rs):
  +ds = Digest.all.role(Role.marks(srcs), srcs)
  a = Equal.cong(List<&2, Digest.Digest>, List<&2, F.Finding>,
    m => List.append(&2, F.Finding, List.concat(&2, F.Finding, [Law.check(m), Rules.covers(rs, ds, rs)]),
      Spare.check(ds)),
    Rules.members(ds, rs, ""), D1.part(ds, rs, ""), pk.members(ds, rs, ""))
  b = Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
    c => List.append(&2, F.Finding, List.concat(&2, F.Finding, [Law.check(D1.part(ds, rs, "")), c]),
      Spare.check(ds)),
    Rules.covers(rs, ds, rs), D1.covered(rs, ds, rs), pk.covers(rs, ds, rs))
  Equal.trans(List<&2, F.Finding>, Rules.project(srcs, rs),
    List.append(&2, F.Finding,
      List.concat(&2, F.Finding, [Law.check(D1.part(ds, rs, "")), Rules.covers(rs, ds, rs)]), Spare.check(ds)),
    D1.packed(srcs, rs), a, b)
