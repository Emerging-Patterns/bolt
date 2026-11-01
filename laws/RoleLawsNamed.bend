import Base
import ../src/paths.bend as Paths
import ../src/role.bend as Role

# Roles. The rules that skip or check law and proof files read
# a file's role (src/role.bend), never its path: told a role, each is the
# rule it was, and a file's role by its name is what its path said
# ---------------------------------------------------------------------------

# LAW: by its name, a file is a law file exactly when it is a LAWS.bend
law role_laws_named:
  for +path: String
  {Role.is_laws(Role.of_path(path)) == Paths.is_laws(path) : Bool}
