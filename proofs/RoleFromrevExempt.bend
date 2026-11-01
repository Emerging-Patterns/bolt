# proofs of laws/RoleFromrevExempt.bend
import Base
import ../src/rules/tokens.bend as T
import ../src/role.bend as Role
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../laws/RoleFromrevExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_fromrev_exempt(rr, e, path, _text, toks, _tree, _bound, _items):
  M1.ex.stop(Role.is_law_file(rr), e, _u => Fromrev.walk(T.sig(toks), path))
