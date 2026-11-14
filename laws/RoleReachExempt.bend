import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline

# LAW: reach reports nothing in a proof file, whatever the source holds
law role_reach_exempt:
  for +max: U32
  for r: Role.Role
  for e: {Role.is_proof(r) == True{} : Bool}
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Reach.check.role(r, Src.Src{path, text, toks, tree, bound, items}, max) == Nil{} : List<&2, F.Finding>}
