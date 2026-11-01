# proofs of laws/RoleClosed.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/laws/closed.bend as Closed
import ../laws/RoleClosed.bend as Laws
import ../laws/RoleLawsNamed.bend as L1
import ./lemmas/RoleLawsPicked.bend as M1

def Laws.role_closed(path, _text, _toks, tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Bool.not(z), [], _u => Closed.check.go(tree, path)),
    Role.is_laws(Role.of_path(path)), Paths.is_laws(path),
    L1.role_laws_named(path))
