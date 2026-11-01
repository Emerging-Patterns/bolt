# proofs of laws/RoleRewalk.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/rewalk.bend as Rewalk
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleRewalk.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_rewalk(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Rewalk.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.rewalk_exempt(path, text, toks, tree, bound, items, e))
