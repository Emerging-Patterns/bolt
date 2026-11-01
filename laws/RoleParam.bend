import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline

# LAW: param told a file's role by its name finds what param finds
law role_param:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Param.check.role(Role.of_path(path), Src.Src{path, text, toks, tree, bound, items})
    == Param.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}
