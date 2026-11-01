# roles picked by name are law or proof files exactly when so named
import Base
import ../../src/paths.bend as Paths
import ../../src/role.bend as Role
import ../../laws/RoleLawFileNamed.bend as L1

# a role picked by name is a law or proof file exactly when either test held
law role.pick_law_file:
  for a: Bool
  for b: Bool
  {Role.is_law_file(Bool.pick(Role.Role, a, Role.Laws{}, Bool.pick(Role.Role, b, Role.Proof{}, Role.Plain{})))
    == Bool.or(a, b) : Bool}

def role.pick_law_file(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def L1.role_law_file_named(path):
  role.pick_law_file(Paths.is_laws(path), Paths.is_proof(path))
