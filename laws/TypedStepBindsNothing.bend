# A do-step written `T <- m`, one capitalized or dotted name and then `<-`
# with no `: A` between them, binds nothing: bend 2.0.40 reads the name as
# the type m runs at (`Unit <- IO.print(..)`, `Bool <- Chan.send(..)`), and
# bend says so itself ("`_ <- m` runs m at type _; to bind its result, write
# `_ : A <- m`"). So the tree reads such a statement as a term, never a let:
# the binder sees the name as a use of a type, `unused` has nothing to report
# on it, and the language server hovers and colors it as a type. Every other
# statement is read as before. A lower-case `x <- m` stays a let: bend 2.0.40
# refuses it ("expected a defined name") unless x names a type, and code
# written for the dialect before it, where `x <- m` bound x, still reads as
# that dialect meant. `X : A <- m` binds X, as any annotated bind does.
# Internal behavior of src/syntax/tree.bend, not interface.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree

# LAW: a statement led by a capitalized name and then `<-` is a term,
# whatever the name and whatever follows
law typed_step_term:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, x, xl, xc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}) == Tree.STerm{} : Tree.StmtKind}

# LAW: a statement led by a dotted name and then `<-` is a term, whatever the
# name and whatever follows
law dotted_step_term:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, x, xl, xc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}) == Tree.STerm{} : Tree.StmtKind}

# LAW: a statement led by a lower-case name and then `<-` is a let, whatever
# the name and whatever follows
law named_bind_let:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}) == Tree.SLet{} : Tree.StmtKind}

# LAW: a statement led by a capitalized name and a `:` is a let exactly when
# a `=` or `<-` follows, as before: an annotation keeps its binder
law annotated_bind_let:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ct: String
  for +cl: U32
  for +cc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, x, xl, xc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}})
    == Bool.pick(Tree.StmtKind, Tree.binds_in(rest), Tree.SLet{}, Tree.STerm{}) : Tree.StmtKind}
