# proofs of laws/RoleParam.bend
import Base
import ../src/finding.bend as F
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../laws/RoleParam.bend as Laws
import ../laws/RoleProofNamed.bend as L1
import ./lemmas/RoleProofPicked.bend as M1

def Laws.role_param(path, _text, _toks, _tree, bound, _items):
  match bound:
    case Bind.Bound{binds, _uses, _scopes}:
      Equal.cong(Bool, List<&2, F.Finding>,
        z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Param.check.go(binds, path)),
        Role.is_proof(Role.of_path(path)), Paths.is_proof(path), L1.role_proof_named(path))
