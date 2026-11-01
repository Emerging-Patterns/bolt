# proofs of laws/RolePrefix.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/prefix.bend as Prefix
import ../laws/RolePrefix.bend as Laws
import ../laws/RoleLawFileNamed.bend as L1
import ./lemmas/RoleLawFilePicked.bend as M1

def Laws.role_prefix(path, _text, toks, _tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Prefix.walk(T.sig(toks), path)),
    Role.is_law_file(Role.of_path(path)), Paths.is_law_file(path),
    L1.role_law_file_named(path))
