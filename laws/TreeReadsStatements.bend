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
def trees.keyword_kind(+tt: String) -> Tree.StmtKind:
  Bool.pick(Tree.StmtKind, String.eq(tt, "def"), Tree.SDef{},
    Bool.pick(Tree.StmtKind, String.eq(tt, "type"), Tree.SType{},
      Bool.pick(Tree.StmtKind, String.eq(tt, "law"), Tree.SLaw{},
        Bool.pick(Tree.StmtKind, String.eq(tt, "import"), Tree.SImport{},
          Bool.pick(Tree.StmtKind, String.eq(tt, "case"), Tree.SCase{},
            Bool.pick(Tree.StmtKind, Bool.or(String.eq(tt, "for"), String.eq(tt, "exs")), Tree.SFor{}, Tree.STerm{}))))))

# LAW: an operator opens type arguments exactly when it is `<` or `<&` glued
# to what is before it
law angle_opens_when_glued:
  for kk: Lex.TokKind
  for +tt: String
  for glued: Bool
  {Tree.opens_angle(kk, tt, glued)
    == Bool.and(D1.kinds.among(kk, [Lex.TOp{}]), Bool.and(glued, Bool.or(String.eq(tt, "<"), String.eq(tt, "<&"))))
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
  for +tt: String
  {Tree.keyword_kind(tt) == trees.keyword_kind(tt) : Tree.StmtKind}

# LAW: the chain after an `@` names a binder exactly when it starts with a
# name, capitalized or not, and then a `:`
law arrow_names_a_binder:
  for +rest: Tree.Node
  {Tree.arrow.named(rest)
    == Bool.and(D2.chains.leaf_of(D2.chains.front(rest), [Lex.TName{}, Lex.TUpper{}]),
      D2.chains.leaf_of(D2.chains.front(D2.chains.after(rest)), [Lex.TColon{}])) : Bool}
