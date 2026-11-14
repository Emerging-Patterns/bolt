# A def's signature is its header through the `:` that ends it, however the
# header is wrapped. The tree makes a statement of each line outside a
# bracket, so a header that wraps there (`def f(xs: A) ->` then `B:`, or
# `def lemma(..)` then `-> {a == b : T}:`) leaves its later lines as the
# first statements under the def. The cost rules and `coverage` read a def's
# signature and body off `Calls.defs`, which joins them back: when the def's
# own line holds no `:` outside a bracket, the statements under it, first to
# last through the first whose own tokens hold one, are the rest of its
# signature, and its body is what is under that statement and then what
# follows it. So a proof whose return type wraps is a proof (the cost rules
# skip it and `coverage` asks no law of it, as
# laws/ExemptPathsYieldNoFindings.bend and laws/LawNamesEveryItem.bend say of
# any proof), and no rule reads a wrapped return type as the body's first
# statement. Read as before, the def's own line its signature and every
# statement under it its body: a def whose own line holds a `:` (one with an
# inline body included), a def with no statement under it that holds one,
# and a def where a statement before that one has statements of its own
# under it. Internal behavior of src/rules/calls.bend, not interface.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/rules/calls.bend as Calls

# LAW: Calls.defs gives each def the signature and the body read here, and
# drops a def with no name as before
law defs_read_header:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  {Calls.defs(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest})
    == Calls.defs.push(Bind.declared(kids), Calls.header(kids, body), Calls.under(kids, body), Calls.defs(rest))
    : List<&2, Calls.Def>}

# LAW: a def whose own line holds a `:` has that line as its signature,
# whatever is under it
law one_line_header:
  for +kids: Tree.Node
  for +body: Tree.Node
  for e: {Calls.has_colon(kids) == True{} : Bool}
  {Calls.header(kids, body) == kids : Tree.Node}

# LAW: a def whose own line holds a `:` has every statement under it as its
# body
law one_line_body:
  for +kids: Tree.Node
  for +body: Tree.Node
  for e: {Calls.has_colon(kids) == True{} : Bool}
  {Calls.under(kids, body) == body : Tree.Node}

# LAW: a header wrapped once: when the def's own line holds no `:` and the
# first statement under it does, that statement's tokens end the signature
law wrapped_header:
  for +kids: Tree.Node
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +below: Tree.Node
  for +rest: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line) == True{} : Bool}
  {Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}) == Calls.join(kids, line) : Tree.Node}

# LAW: a header wrapped once: the body is what is under the statement that
# ends it, then what follows it
law wrapped_body:
  for +kids: Tree.Node
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +below: Tree.Node
  for +rest: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line) == True{} : Bool}
  {Calls.under(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}) == Calls.join(below, rest) : Tree.Node}

# LAW: a header wrapped twice: a statement with no `:` and nothing under it
# is passed through, its tokens kept in order, to the one that holds the `:`
law wrapped_twice_header:
  for +kids: Tree.Node
  for +k1: Tree.StmtKind
  for +line1: Tree.Node
  for +k2: Tree.StmtKind
  for +line2: Tree.Node
  for +below: Tree.Node
  for +rest: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line1) == False{} : Bool}
  for e2: {Calls.has_colon(line2) == True{} : Bool}
  {Calls.header(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}})
    == Calls.join(kids, Calls.join(line1, line2)) : Tree.Node}

# LAW: a header wrapped twice: the body is what is under the statement that
# ends it, then what follows it
law wrapped_twice_body:
  for +kids: Tree.Node
  for +k1: Tree.StmtKind
  for +line1: Tree.Node
  for +k2: Tree.StmtKind
  for +line2: Tree.Node
  for +below: Tree.Node
  for +rest: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line1) == False{} : Bool}
  for e2: {Calls.has_colon(line2) == True{} : Bool}
  {Calls.under(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}})
    == Calls.join(below, rest) : Tree.Node}

# LAW: a def with no `:` on its own line and none on the one statement under
# it is read as before: its own line is the signature
law unended_header:
  for +kids: Tree.Node
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +below: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}) == kids : Tree.Node}

# LAW: a def with no `:` on its own line and none on the one statement under
# it is read as before: that statement is its body
law unended_body:
  for +kids: Tree.Node
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +below: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.under(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}})
    == Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}} : Tree.Node}

# LAW: a statement before the `:` that has statements of its own under it
# stops the reading: the def's own line is its signature, as before
law nested_line_header:
  for +kids: Tree.Node
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +inner: Tree.Node
  for +more: Tree.Node
  for +rest: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest}) == kids : Tree.Node}

# LAW: a def with a typed parameter list on its own line and `-> {..}:` on
# the next is a proof, whatever the names, the parameters, the claim, and
# whatever is under either line
law arrow_below_is_proof:
  for +dt: String
  for +dl: U32
  for +dc: U32
  for +nt: String
  for +nl: U32
  for +nc: U32
  for +po: Lex.Tok
  for +pk: Tree.Node
  for +pc: Maybe<&2, Lex.Tok>
  for +kind: Tree.StmtKind
  for +at: String
  for +al: U32
  for +ac: U32
  for +bl: U32
  for +bc: U32
  for +bk: Tree.Node
  for +bz: Maybe<&2, Lex.Tok>
  for +ct: String
  for +cl: U32
  for +c: U32
  for +below: Tree.Node
  for +rest: Tree.Node
  {Calls.proof(Calls.header(
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, dt, dl, dc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, nt, nl, nc}}, Tree.NCons{Tree.Group{po, pk, pc}, Tree.NNil{}}}},
    Tree.NCons{Tree.Stmt{kind,
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TArrow{}, at, al, ac}},
        Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "{", bl, bc}, bk, bz},
          Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, c}}, Tree.NNil{}}}},
      below}, rest})) == True{} : Bool}

# LAW: a def whose own line ends in `->` with `{..}:` on the next is a
# proof, whatever the names, the parameters, the claim, and whatever is under
# either line
law type_below_is_proof:
  for +dt: String
  for +dl: U32
  for +dc: U32
  for +nt: String
  for +nl: U32
  for +nc: U32
  for +po: Lex.Tok
  for +pk: Tree.Node
  for +pc: Maybe<&2, Lex.Tok>
  for +kind: Tree.StmtKind
  for +at: String
  for +al: U32
  for +ac: U32
  for +bl: U32
  for +bc: U32
  for +bk: Tree.Node
  for +bz: Maybe<&2, Lex.Tok>
  for +ct: String
  for +cl: U32
  for +c: U32
  for +below: Tree.Node
  for +rest: Tree.Node
  {Calls.proof(Calls.header(
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, dt, dl, dc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, nt, nl, nc}},
        Tree.NCons{Tree.Group{po, pk, pc},
          Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TArrow{}, at, al, ac}}, Tree.NNil{}}}}},
    Tree.NCons{Tree.Stmt{kind,
      Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "{", bl, bc}, bk, bz},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, c}}, Tree.NNil{}}},
      below}, rest})) == True{} : Bool}
