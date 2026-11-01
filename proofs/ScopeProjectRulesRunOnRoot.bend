# proofs of laws/ScopeProjectRulesRunOnRoot.bend
import Base
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../src/role.bend as Role
import ../src/rules/digest.bend as Digest
import ../src/rules/laws/law.bend as Law
import ../laws/ScopeProjectRulesRunOnRoot.bend as Laws

# with no root but `.`, every directory's package is `.`
law pk.go_none:
  for us: List<&2, String>
  {Rules.owner.go(us, []) == "" : String}

def pk.go_none(us):
  match us:
    case Nil{}:
      {==}
    case Con{_u, +tl}:
      pk.go_none(tl)

# with no root but `.`, the package `.` holds every file
law pk.none:
  for ds: List<&2, Digest.Digest>
  {Rules.members(ds, [], "") == ds : List<&2, Digest.Digest>}

def pk.none(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, +dir, +is_laws, +is_law_file, +exempt, +tops, +says, +deps, +laws},
      +tl}:
      o = Equal.sym(String, Rules.owner.go(Rules.ups(dir), []), "", pk.go_none(Rules.ups(dir)))
      %o : {Bool.pick(List<&2, Digest.Digest>, String.eq(_, ""),
          Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}
            <> Rules.members(tl, [], ""), Rules.members(tl, [], ""))
        == Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws} <> tl
        : List<&2, Digest.Digest>}
      Equal.cong(List<&2, Digest.Digest>, List<&2, Digest.Digest>,
        xs => Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws} <> xs,
        Rules.members(tl, [], ""), tl, pk.none(tl))

def Laws.one_package(s, ss):
  +ds = Digest.all.role(Role.marks(s <> ss), s <> ss)
  Equal.cong(List<&2, Digest.Digest>, List<&2, F.Finding>,
    mm => List.concat(&2, F.Finding, [Law.check(mm), []]),
    Rules.members(ds, [], ""), ds, pk.none(ds))
