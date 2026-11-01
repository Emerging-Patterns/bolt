# proofs of laws/RoleNamedFirst.bend
import Base
import ../src/role.bend as Role
import ../laws/RoleNamedFirst.bend as Laws

def Laws.role_named_first(named, reach, e):
  s = Equal.sym(Bool, Role.is_law_file(named), True{}, e)
  %s : {Bool.pick(Role.Role, _, named, reach) == named : Role.Role}
  {==}
