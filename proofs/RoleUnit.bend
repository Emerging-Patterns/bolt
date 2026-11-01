# proofs of laws/RoleUnit.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/unit.bend as UnitRule
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleUnit.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_unit(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => UnitRule.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.unit_exempt(path, text, toks, tree, bound, items, e))
