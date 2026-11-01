# proofs of laws/RoleDocExempt.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/doc.bend as Doc
import ../laws/RoleDocExempt.bend as Laws

def Laws.role_doc_exempt(rr, e, path, text, toks, _tree, _bound, items):
  s = Equal.sym(Bool, Role.is_proof(rr), True{}, e)
  %s : {Lazy.stop(List<&2, F.Finding>, Bool.or(_, Paths.is_test(path)), [],
      _u => Doc.check.go(items, path, Doc.lines(text, toks)))
    == Nil{} : List<&2, F.Finding>}
  {==}
