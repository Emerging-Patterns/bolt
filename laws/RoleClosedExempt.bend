import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/laws/closed.bend as Closed

# LAW: closed reports nothing in a file that is not a law file, whatever the source holds
law role_closed_exempt:
  for r: Role.Role
  for e: {Role.is_laws(r) == False{} : Bool}
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Closed.check.role(r, Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}
