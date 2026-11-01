import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree

# LAW: so is one whose name carries a quantity mark (`@+x:`, `@-x:`)
law marked_arrow_term:
  for +at: String
  for +al: U32
  for +ac: U32
  for +mt: String
  for +ml: U32
  for +mc: U32
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ct: String
  for +cl: U32
  for +cc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, at, al, ac}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, mt, ml, mc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}}}) == Tree.STerm{} : Tree.StmtKind}
