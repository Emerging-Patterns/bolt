# proofs of laws/RoleReachExempt.bend
import Base
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../laws/RoleReachExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_reach_exempt(max, r, e, path, _text, toks, _tree, bound, _items):
  match bound:
    case Bind.Bound{binds, uses, _scopes}:
      M1.ex.stop(Role.is_proof(r), e, _u => Reach.check.far(Reach.far(uses, max), binds, toks, path, max))
