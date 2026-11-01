# proofs of laws/RoleConcat.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/concat.bend as Concat
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleConcat.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_concat(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Concat.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.concat_exempt(path, text, toks, tree, bound, items, e))
