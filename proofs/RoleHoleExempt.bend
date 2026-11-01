# proofs of laws/RoleHoleExempt.bend
import Base
import ../src/role.bend as Role
import ../src/rules/correctness/hole.bend as Hole
import ../laws/RoleHoleExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_hole_exempt(rr, e, path, _text, toks, _tree, _bound, _items):
  M1.ex.stop(Role.is_laws(rr), e, _u => Hole.check.go(toks, path))
