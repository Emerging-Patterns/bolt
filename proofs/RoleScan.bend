# proofs of laws/RoleScan.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/scan.bend as Scan
import ../laws/RoleLawFileNamed.bend as L1
import ../laws/RoleScan.bend as Laws
import ./lemmas/RoleLawFilePicked.bend as M1

def Laws.role_scan(path, _text, _toks, tree, _bound, _items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, z, [], _u => Scan.check.on(Calls.defs(tree), path)),
    Role.is_law_file(Role.of_path(path)), Paths.is_law_file(path),
    L1.role_law_file_named(path))
