# proofs of laws/RoleDoc.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/doc.bend as Doc
import ../laws/RoleDoc.bend as Laws
import ../laws/RoleProofNamed.bend as L1
import ./lemmas/RoleProofPicked.bend as M1

def Laws.role_doc(path, text, toks, _tree, _bound, items):
  Equal.cong(Bool, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Bool.or(z, Paths.is_test(path)), [],
    _u => Doc.check.go(items, path, Doc.lines(text, toks))), Role.is_proof(Role.of_path(path)), Paths.is_proof(path),
    L1.role_proof_named(path))
