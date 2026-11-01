# proofs of laws/RoleTable.bend
import Base
import ../src/src.bend as Src
import ../src/rules/suspicious/table.bend as Table
import ../laws/ExemptPathsYieldNoFindings.bend as L1
import ../laws/RoleTable.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

def Laws.role_table(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Table.check(Src.Src{path, text, toks, tree, bound, items}),
    e => L1.table_exempt(path, text, toks, tree, bound, items, e))
