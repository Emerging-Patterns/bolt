# proofs of laws/RoleParamExempt.bend
import Base
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../laws/RoleParamExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_param_exempt(rr, e, path, _text, _toks, _tree, bound, _items):
  match bound:
    case Bind.Bound{binds, _uses, _scopes}:
      M1.ex.stop(Role.is_proof(rr), e, _u => Param.check.go(binds, path))
