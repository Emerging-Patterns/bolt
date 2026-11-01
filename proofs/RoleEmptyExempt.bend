# proofs of laws/RoleEmptyExempt.bend
import Base
import ../src/rules/tokens.bend as T
import ../src/role.bend as Role
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/RoleEmptyExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_empty_exempt(rr, e, path, _text, toks, _tree, _bound, _items):
  M1.ex.stop(Role.is_law_file(rr), e, _u => Empty.walk(T.sig(toks), path, False{}))
