# An array write `a[i] <- v` reads the array a and keeps its name: as the
# last statement it is the written array, and before another statement it
# is `a = a[i] <- v` (the guide), the same name for the written array. So
# the tree reads such a statement as a term, never a let: the binder sees a,
# and every name inside the brackets and after the `<-`, as uses. `unused`
# then counts the write as a use of a, as bend does, and never reports the
# array or an index (`def f(a, i) -> Array<U32>: a[i] <- 7` uses both).
# A later use of a resolves to the binder a already had. A write into what
# a parenthesized term gives, `(a[i] <- v)[j] <- w` (writes chained in one
# term), is read the same way: a `(..)` group, a `[..]` group and then `<-`
# is a term, so the names in the parentheses are uses too. A statement whose
# name is followed by any other group, or by `[..]` and then no `<-`, reads
# as before, and so does one led by a `(..)` group that any other group
# follows, or by a `[..]` group. Internal behavior of src/syntax/tree.bend,
# not interface.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree

# LAW: a statement led by a name, a `[..]` group and then `<-` is a term,
# whatever the name, the index and whatever follows
law array_write_term:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}}) == Tree.STerm{} : Tree.StmtKind}

# LAW: a statement led by a name, a `(..)` group and then `<-` reads as it
# did: a let exactly when a `=` or `<-` is among its tokens, which it is
law paren_group_let:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}}) == Tree.SLet{} : Tree.StmtKind}

# LAW: a statement led by a name, a `[..]` group and a `=` is a let, as
# before: `a[i] = v` is no write
law index_eq_let:
  for +x: String
  for +xl: U32
  for +xc: U32
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +et: String
  for +el: U32
  for +ec: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, et, el, ec}}, rest}}}) == Tree.SLet{} : Tree.StmtKind}

# LAW: a statement led by a `(..)` group, a `[..]` group and then `<-` is a
# term, whatever the parentheses hold, the index and whatever follows
law chained_write_term:
  for +pl: U32
  for +pc: U32
  for +ps: Tree.Node
  for +pz: Maybe<&2, Lex.Tok>
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", pl, pc}, ps, pz},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}}) == Tree.STerm{} : Tree.StmtKind}

# LAW: a statement led by two `(..)` groups and then `<-` reads as it did: a
# let, since a `<-` is among its tokens
law paren_pair_let:
  for +pl: U32
  for +pc: U32
  for +ps: Tree.Node
  for +pz: Maybe<&2, Lex.Tok>
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", pl, pc}, ps, pz},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}}) == Tree.SLet{} : Tree.StmtKind}

# LAW: a statement led by two `[..]` groups and then `<-` reads as it did: a
# let, since a `<-` is among its tokens
law bracket_pair_let:
  for +pl: U32
  for +pc: U32
  for +ps: Tree.Node
  for +pz: Maybe<&2, Lex.Tok>
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +bt: String
  for +bl: U32
  for +bc: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", pl, pc}, ps, pz},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, bt, bl, bc}}, rest}}}) == Tree.SLet{} : Tree.StmtKind}

# LAW: a statement led by a `(..)` group, a `[..]` group and a `=` is a let,
# as before: only `<-` writes
law paren_index_eq_let:
  for +pl: U32
  for +pc: U32
  for +ps: Tree.Node
  for +pz: Maybe<&2, Lex.Tok>
  for +ol: U32
  for +oc: U32
  for +gs: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +et: String
  for +el: U32
  for +ec: U32
  for +rest: Tree.Node
  {Tree.classify(Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", pl, pc}, ps, pz},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "[", ol, oc}, gs, cl},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, et, el, ec}}, rest}}}) == Tree.SLet{} : Tree.StmtKind}
