import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree

# LAW: a statement led by an attribute, `@` and a name then a keyword
# (`@unsafe def`), is a def, whatever follows
law attribute_def:
  for +at: String
  for +al: U32
  for +ac: U32
  for +x: String
  for +xl: U32
  for +xc: U32
  for +kt: String
  for +kl: U32
  for +kc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, at, al, ac}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x,
    xl, xc}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, kt, kl, kc}}, rest}}}) == Tree.SDef{} : Tree.StmtKind}
