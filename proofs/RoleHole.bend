# proofs of laws/RoleHole.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/correctness/hole.bend as Hole
import ../laws/RoleHole.bend as Laws
import ../laws/RoleLawsNamed.bend as L1
import ./lemmas/RoleLawsPicked.bend as M1

def Laws.role_hole(path, _text, toks, _tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Hole.check.go(toks, path)),
    Role.is_laws(Role.of_path(path)), Paths.is_laws(path),
    L1.role_laws_named(path))
