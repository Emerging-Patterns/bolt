import Base
import ../src/paths.bend as Paths
import ../src/role.bend as Role

# LAW: by its name, a file is a law or proof file exactly when it is a
# LAWS.bend or a PROOF.bend
law role_law_file_named:
  for +path: String
  {Role.is_law_file(Role.of_path(path)) == Paths.is_law_file(path) : Bool}
