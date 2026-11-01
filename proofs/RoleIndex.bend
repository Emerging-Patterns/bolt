# proofs of laws/RoleIndex.bend
import Base
import ../src/src.bend as Src
import ../src/rules/pedantic/index.bend as Index
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleIndex.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_index(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Index.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.index_exempt(path, text, toks, tree, bound, items, e))
