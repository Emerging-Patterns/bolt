# proofs of laws/RoleFromrev.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../laws/RoleFromrev.bend as Laws
import ../laws/RoleLawFileNamed.bend as L1
import ./lemmas/RoleLawFilePicked.bend as M1

def Laws.role_fromrev(path, _text, toks, _tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Fromrev.walk(T.sig(toks), path)),
    Role.is_law_file(Role.of_path(path)), Paths.is_law_file(path),
    L1.role_law_file_named(path))
