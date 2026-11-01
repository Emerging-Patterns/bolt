# proofs of laws/RolePrefixExempt.bend
import Base
import ../src/rules/tokens.bend as T
import ../src/role.bend as Role
import ../src/rules/suspicious/prefix.bend as Prefix
import ../laws/RolePrefixExempt.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_prefix_exempt(rr, e, path, _text, toks, _tree, _bound, _items):
  M1.ex.stop(Role.is_law_file(rr), e, _u => Prefix.walk(T.sig(toks), path))
