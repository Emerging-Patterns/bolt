# proofs of laws/RoleClosedExempt.bend
import Base
import ../src/finding.bend as F
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/laws/closed.bend as Closed
import ../laws/RoleClosedExempt.bend as Laws

def Laws.role_closed_exempt(rr, e, path, _text, _toks, tree, _bound, _items):
  s = Equal.sym(Bool, Role.is_laws(rr), False{}, e)
  %s : {Lazy.stop(List<&2, F.Finding>, Bool.not(_), [], _u => Closed.check.go(tree, path))
    == Nil{} : List<&2, F.Finding>}
  {==}
