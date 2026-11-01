# proofs of laws/RoleHoist.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/hoist.bend as Hoist
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleHoist.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_hoist(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Hoist.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.hoist_exempt(path, text, toks, tree, bound, items, e))
