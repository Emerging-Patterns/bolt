# proofs of laws/RoleEager.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/eager.bend as Eager
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleEager.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_eager(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Eager.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.eager_exempt(path, text, toks, tree, bound, items, e))
