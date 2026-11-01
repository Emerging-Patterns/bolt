import Base
import ../src/role.bend as Role

# LAW: any other file has the role it has once reached
law role_reached:
  for +named: Role.Role
  for reach: Role.Role
  for e: {Role.is_law_file(named) == False{} : Bool}
  {Role.role.of(named, reach) == reach : Role.Role}
