# proofs of laws/RoleReach.bend
import Base
import ../src/finding.bend as F
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../laws/RoleReach.bend as Laws
import ../laws/RoleProofNamed.bend as L1
import ./lemmas/RoleProofPicked.bend as M1

def Laws.role_reach(path, _text, toks, _tree, bound, _items):
  match bound:
    case Bind.Bound{binds, uses, _scopes}:
      Equal.cong(Bool, List<&2, F.Finding>,
        z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Reach.check.far(Reach.far(uses), binds, toks, path)),
        Role.is_proof(Role.of_path(path)), Paths.is_proof(path), L1.role_proof_named(path))
