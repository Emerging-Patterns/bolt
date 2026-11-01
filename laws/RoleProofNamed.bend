import Base
import ../src/paths.bend as Paths
import ../src/role.bend as Role

# LAW: by its name, a file is a proof file exactly when it is a PROOF.bend
law role_proof_named:
  for +path: String
  {Role.is_proof(Role.of_path(path)) == Paths.is_proof(path) : Bool}
