# proofs of laws/RolePick.bend
import Base
import ../src/src.bend as Src
import ../src/rules/correctness/pick.bend as Pick
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RolePick.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_pick(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Pick.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.pick_exempt(path, text, toks, tree, bound, items, e))
