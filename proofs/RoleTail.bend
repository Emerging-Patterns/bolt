# proofs of laws/RoleTail.bend
import Base
import ../src/src.bend as Src
import ../src/rules/pedantic/tail.bend as Tail
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleTail.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_tail(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Tail.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.tail_exempt(path, text, toks, tree, bound, items, e))
