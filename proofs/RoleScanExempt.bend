# proofs of laws/RoleScanExempt.bend
import Base
import ../src/role.bend as Role
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/scan.bend as Scan
import ../laws/RoleScanExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_scan_exempt(rr, e, path, _text, _toks, tree, _bound, _items):
  M1.ex.stop(Role.is_law_file(rr), e, _u => Scan.check.on(Calls.defs(tree), path))
