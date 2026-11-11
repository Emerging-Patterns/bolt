import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/blank.bend as Blank

# LAW: blank reports nothing in a law or proof file, whatever the source holds
law role_blank_exempt:
  for rr: Role.Role
  for e: {Role.is_law_file(rr) == True{} : Bool}
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Blank.check.role(rr, Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}
