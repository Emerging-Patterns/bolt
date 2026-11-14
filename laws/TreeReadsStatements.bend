# How the tree is built from tokens, where a rule depends on it. A `<` or
# `<&` glued to the name before it opens type arguments, and nowhere else
# (so `a < b` is a comparison). A statement binds when a `=` or a `<-` stands
# among its own tokens, not inside a group. A statement's kind is its
# keyword's: `def`, `type`, `law`, `import`, `case`, and `for` or `exs`
# (a law's binder lines); any other is a term. After an `@`, a name and a `:`
# are a binder.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ./defs/TokenKinds.bend as D1
import ./defs/Chains.bend as D2

# a statement's kind by its keyword. Law vocabulary: bolt never calls it
def trees.keyword_kind(+t: String) -> Tree.StmtKind:
  Bool.pick(Tree.StmtKind, String.eq(t, "def"), Tree.SDef{},
    Bool.pick(Tree.StmtKind, String.eq(t, "type"), Tree.SType{},
      Bool.pick(Tree.StmtKind, String.eq(t, "law"), Tree.SLaw{},
        Bool.pick(Tree.StmtKind, String.eq(t, "import"), Tree.SImport{},
          Bool.pick(Tree.StmtKind, String.eq(t, "case"), Tree.SCase{},
            Bool.pick(Tree.StmtKind, Bool.or(String.eq(t, "for"), String.eq(t, "exs")), Tree.SFor{}, Tree.STerm{}))))))

# LAW: an operator opens type arguments exactly when it is `<` or `<&` glued
# to what is before it
law angle_opens_when_glued:
  for k: Lex.TokKind
  for +t: String
  for glued: Bool
  {Tree.opens_angle(k, t, glued)
    == Bool.and(D1.kinds.among(k, [Lex.TOp{}]), Bool.and(glued, Bool.or(String.eq(t, "<"), String.eq(t, "<&"))))
    : Bool}

# LAW: a statement binds when its first node is a `=` or a `<-`, or when the
# rest of its own tokens bind
law binds_in_own_tokens:
  for h: Tree.Node
  for rest: Tree.Node
  {Tree.binds_in(Tree.NCons{h, rest})
    == Bool.or(D2.chains.node_of(h, [Lex.TEq{}, Lex.TBind{}]), Tree.binds_in(rest)) : Bool}

# LAW: what is no chain binds nothing
law binds_in_needs_tokens:
  for kids: Tree.Node
  for e: {D2.chains.is_cons(kids) == False{} : Bool}
  {Tree.binds_in(kids) == False{} : Bool}

# LAW: a statement's kind is read off its keyword
law statement_kind_by_keyword:
  for +t: String
  {Tree.keyword_kind(t) == trees.keyword_kind(t) : Tree.StmtKind}

# LAW: the chain after an `@` names a binder exactly when it starts with a
# name, capitalized or not, and then a `:`
law arrow_names_a_binder:
  for +rest: Tree.Node
  {Tree.arrow.named(rest)
    == Bool.and(D2.chains.leaf_of(D2.chains.front(rest), [Lex.TName{}, Lex.TUpper{}]),
      D2.chains.leaf_of(D2.chains.front(D2.chains.after(rest)), [Lex.TColon{}])) : Bool}

# LAW: a line ends the open statement on top when that statement is at its
# column or deeper, and then asks the one below
law deeper_ends_a_statement_at_or_past_the_column:
  for +indent: U32
  for kids: Tree.Node
  for body: Tree.Node
  for +rest: List<&2, Tree.Frame>
  for +col: U32
  for e: {U32.is_ge(indent, col) == True{} : Bool}
  {Tree.deeper(Tree.FStmt{indent, kids, body} <> rest, col) == Succ{Tree.deeper(rest, col)} : Nat}

# LAW: a statement shallower than the line stays open, and so does every one
# below it
law deeper_stops_at_a_shallower_statement:
  for +indent: U32
  for kids: Tree.Node
  for body: Tree.Node
  for +rest: List<&2, Tree.Frame>
  for +col: U32
  for e: {U32.is_ge(indent, col) == False{} : Bool}
  {Tree.deeper(Tree.FStmt{indent, kids, body} <> rest, col) == 0n : Nat}

# LAW: a statement with nothing under it shows as its tokens in brackets
law show_statement_alone:
  for kind: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for e: {String.is_empty(Tree.show(body)) == True{} : Bool}
  {Tree.show(Tree.Stmt{kind, kids, body}) == "[" ++ Tree.show(kids) ++ "" ++ "]" : String}

# LAW: and with its body in braces after them when it has one
law show_statement_with_body:
  for kind: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for e: {String.is_empty(Tree.show(body)) == False{} : Bool}
  {Tree.show(Tree.Stmt{kind, kids, body}) == "[" ++ Tree.show(kids) ++ (" {" ++ Tree.show(body) ++ "}") ++ "]"
    : String}

# LAW: the last node of a chain shows alone
law show_last_node:
  for +h: Tree.Node
  for +t: Tree.Node
  for e: {String.is_empty(Tree.show(t)) == True{} : Bool}
  {Tree.show(Tree.NCons{h, t}) == Tree.show(h) ++ "" : String}

# LAW: any other with a space before what follows it
law show_node_then_rest:
  for +h: Tree.Node
  for +t: Tree.Node
  for e: {String.is_empty(Tree.show(t)) == False{} : Bool}
  {Tree.show(Tree.NCons{h, t}) == Tree.show(h) ++ (" " ++ Tree.show(t)) : String}

# LAW: a group that never closed shows `..` where its close would be
law show_unclosed_group:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for kids: Tree.Node
  {Tree.show(Tree.Group{Lex.Tok{k, t, l, c}, kids, None{}}) == t ++ Tree.show(kids) ++ ".." : String}
