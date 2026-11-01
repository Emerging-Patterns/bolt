import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/hole.bend as Hole
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline

# LAW: hole told a file's role by its name finds what hole finds
law role_hole:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Hole.check.role(Role.of_path(path), Src.Src{path, text, toks, tree, bound, items})
    == Hole.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}
