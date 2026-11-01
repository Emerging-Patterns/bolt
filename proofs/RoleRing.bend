# proofs of laws/RoleRing.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/ring.bend as Ring
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleRing.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_ring(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Ring.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.ring_exempt(path, text, toks, tree, bound, items, e))
