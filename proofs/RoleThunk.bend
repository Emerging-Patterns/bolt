# proofs of laws/RoleThunk.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/thunk.bend as Thunk
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleThunk.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_thunk(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Thunk.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.thunk_exempt(path, text, toks, tree, bound, items, e))
