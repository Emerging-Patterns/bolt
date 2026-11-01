# proofs of laws/RoleReached.bend
import Base
import ../src/role.bend as Role
import ../laws/RoleReached.bend as Laws

def Laws.role_reached(named, reach, e):
  s = Equal.sym(Bool, Role.is_law_file(named), False{}, e)
  %s : {Bool.pick(Role.Role, _, named, reach) == reach : Role.Role}
  {==}
