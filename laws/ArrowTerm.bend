import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree

# LAW: a statement led by `@`, a name and a `:` is a dependent arrow, a term,
# never a def, whatever the name and whatever follows
law arrow_term:
  for +at: String
  for +al: U32
  for +ac: U32
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ct: String
  for +cl: U32
  for +cc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, at, al, ac}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x,
    xl, xc}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}}) == Tree.STerm{} : Tree.StmtKind}
