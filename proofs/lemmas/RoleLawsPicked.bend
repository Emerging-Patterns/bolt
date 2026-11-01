# roles picked by name for the laws files
import Base
import ../../src/paths.bend as Paths
import ../../src/role.bend as Role
import ../../laws/RoleLawsNamed.bend as L1

# roles
# -----

# a role picked by name is a law file exactly when the first test held
law role.pick_laws:
  for a: Bool
  for b: Bool
  {Role.is_laws(Bool.pick(Role.Role, a, Role.Laws{}, Bool.pick(Role.Role, b, Role.Proof{}, Role.Plain{}))) == a : Bool}

def role.pick_laws(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def L1.role_laws_named(path):
  role.pick_laws(Paths.is_laws(path), Paths.is_proof(path))
