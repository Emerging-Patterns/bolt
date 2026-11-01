import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/rewalk.bend as Rewalk

# LAW: rewalk, which checks nothing in a law or proof file, told a file's role
# by its name finds what rewalk finds
law role_rewalk:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Role.skip(Role.of_path(path), _u => Rewalk.check(Src.Src{path, text, toks, tree, bound, items}))
    == Rewalk.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}
