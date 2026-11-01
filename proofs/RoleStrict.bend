# proofs of laws/RoleStrict.bend
import Base
import ../src/src.bend as Src
import ../src/rules/pedantic/strict.bend as Strict
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleStrict.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_strict(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Strict.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.strict_exempt(path, text, toks, tree, bound, items, e))
