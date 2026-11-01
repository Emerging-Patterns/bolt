import Base
import ../src/role.bend as Role

# LAW: a LAWS.bend or a PROOF.bend keeps its role by name, whatever it holds
law role_named_first:
  for +named: Role.Role
  for reach: Role.Role
  for e: {Role.is_law_file(named) == True{} : Bool}
  {Role.role.of(named, reach) == named : Role.Role}
