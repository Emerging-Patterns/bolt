# How the binder reads Bend's binding forms. The binder walks a file's tree
# in a mode (a constructor list, a name, a telescope, a pattern, a term, ...)
# and asks of each leaf, by the mode and the leaf's kind and sometimes a peek
# at what follows: does it record a binder, does that binder enter the
# environment, does it use a name, and is it the `=` or `<-` whose right side
# still sees the names outside the let. What resolution then does with the
# binders is laws/BinderResolvesInnermostFirst.bend; this file is which
# tokens are binders and uses in the first place.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ./defs/TokenKinds.bend as D1
import ./defs/Chains.bend as D2

# Law vocabulary, down to the LAWs: bolt never calls any of it.

# does a leaf record a binder? In a constructor list, a capitalized name. In
# a name position, a name, capitalized or dotted. In a telescope, a name, a
# capitalized name, or an operator with a name after it (`+x`). In a
# telescope's type, an `@` with `x:` after it. In a pattern, a name, or a
# capitalized name with no group after it. In a term, a name with `=>` after
# it, an `@` with `x:` or `X:` after it, or an `&` with `x:` after it.
# Nothing else does
def binds.records(mode: Bind.Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Bool:
  match mode kk:
    case Bind.MCtor{} Lex.TUpper{}:
      True{}
    case Bind.MName{} Lex.TName{}:
      True{}
    case Bind.MName{} Lex.TUpper{}:
      True{}
    case Bind.MName{} Lex.TDotted{}:
      True{}
    case Bind.MTele{_kind} Lex.TOp{}:
      Bind.plan.named(rest)
    case Bind.MTele{_kind} Lex.TName{}:
      True{}
    case Bind.MTele{_kind} Lex.TUpper{}:
      True{}
    case Bind.MTeleType{_kind} Lex.TAll{}:
      Bind.plan.typed(rest, False{})
    case Bind.MLhs{_outer, _kind} Lex.TUpper{}:
      Bool.not(Bind.plan.group(rest))
    case Bind.MLhs{_outer, _kind} Lex.TName{}:
      True{}
    case Bind.MTerm{} Lex.TName{}:
      Bind.plan.lam(rest)
    case Bind.MTerm{} Lex.TAll{}:
      Bind.plan.typed(rest, True{})
    case Bind.MTerm{} Lex.TAmp{}:
      Bind.plan.typed(rest, False{})
    case _other _k:
      False{}

# is the mode an item's name or a constructor's? The file's items hold those
# names, so the environment does not
def binds.is_item(mode: Bind.Mode) -> Bool:
  match mode:
    case Bind.MCtor{}:
      True{}
    case Bind.MName{}:
      True{}
    case _other:
      False{}

# does a leaf use a name? In a telescope's type and in a pattern's type, a
# name, capitalized or dotted. In a pattern, a capitalized or dotted name
# with a group after it (a constructor applied). In a term, a capitalized or
# dotted name, or a name with no `=>` after it. Nothing else does
def binds.uses(mode: Bind.Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Bool:
  match mode kk:
    case Bind.MTeleType{_kind} Lex.TName{}:
      True{}
    case Bind.MTeleType{_kind} Lex.TUpper{}:
      True{}
    case Bind.MTeleType{_kind} Lex.TDotted{}:
      True{}
    case Bind.MLhs{_outer, _kind} Lex.TUpper{}:
      Bind.plan.group(rest)
    case Bind.MLhs{_outer, _kind} Lex.TDotted{}:
      Bind.plan.group(rest)
    case Bind.MLhsType{_outer} Lex.TName{}:
      True{}
    case Bind.MLhsType{_outer} Lex.TUpper{}:
      True{}
    case Bind.MLhsType{_outer} Lex.TDotted{}:
      True{}
    case Bind.MTerm{} Lex.TName{}:
      Bool.not(Bind.plan.lam(rest))
    case Bind.MTerm{} Lex.TUpper{}:
      True{}
    case Bind.MTerm{} Lex.TDotted{}:
      True{}
    case _other _k:
      False{}

# is the mode a pattern or a pattern's type?
def binds.is_lhs(mode: Bind.Mode) -> Bool:
  match mode:
    case Bind.MLhs{_outer, _kind}:
      True{}
    case Bind.MLhsType{_outer}:
      True{}
    case _other:
      False{}

# LAW: a chain starts with a `=>` exactly when its first node is a leaf of
# that kind
law plan_lam_leads:
  for rest: Tree.Node
  {Bind.plan.lam(rest) == D2.chains.leaf_of(D2.chains.front(rest), [Lex.TLam{}]) : Bool}

# LAW: a chain starts with a group exactly when its first node is one
law plan_group_leads:
  for rest: Tree.Node
  {Bind.plan.group(rest) == D2.chains.is_group(D2.chains.front(rest)) : Bool}

# LAW: a chain starts with a name exactly when its first node is a name or a
# capitalized name
law plan_named_leads:
  for rest: Tree.Node
  {Bind.plan.named(rest) == D2.chains.leaf_of(D2.chains.front(rest), [Lex.TName{}, Lex.TUpper{}]) : Bool}

# LAW: a chain starts with `x:` exactly when its first node is a name and its
# second a `:`; it starts with `X:` that way only when capitalized names are
# asked for
law plan_typed_leads:
  for +rest: Tree.Node
  for upper: Bool
  {Bind.plan.typed(rest, upper)
    == Bool.or(
      Bool.and(D2.chains.leaf_of(D2.chains.front(rest), [Lex.TName{}]),
        D2.chains.leaf_of(D2.chains.front(D2.chains.after(rest)), [Lex.TColon{}])),
      Bool.and(D2.chains.leaf_of(D2.chains.front(rest), [Lex.TUpper{}]),
        Bool.and(D2.chains.leaf_of(D2.chains.front(D2.chains.after(rest)), [Lex.TColon{}]), upper))) : Bool}

# LAW: a leaf records a binder exactly in the forms binds.records lists
law plan_records:
  for mode: Bind.Mode
  for kk: Lex.TokKind
  for +rest: Tree.Node
  {Bind.plan.rec(mode, kk, rest) == binds.records(mode, kk, rest) : Bool}

# LAW: a recorded binder enters the environment unless it is an item's name
# or a constructor's
law plan_pushes:
  for +mode: Bind.Mode
  for kk: Lex.TokKind
  for +rest: Tree.Node
  {Bind.plan.push(mode, kk, rest) == Bool.and(Bool.not(binds.is_item(mode)), binds.records(mode, kk, rest)) : Bool}

# LAW: a leaf uses a name exactly in the forms binds.uses lists
law plan_uses:
  for mode: Bind.Mode
  for kk: Lex.TokKind
  for +rest: Tree.Node
  {Bind.plan.use(mode, kk, rest) == binds.uses(mode, kk, rest) : Bool}

# LAW: the right side of a let sees the names outside it: the leaf that
# keeps them is the `=` or the `<-` of a pattern or of a pattern's type, and
# no other
law plan_keeps:
  for mode: Bind.Mode
  for +kk: Lex.TokKind
  {Bind.plan.keep(mode, kk) == Bool.and(binds.is_lhs(mode), D1.kinds.among(kk, [Lex.TEq{}, Lex.TBind{}])) : Bool}

# do the names a group binds stay bound after it? A signature's parameters
# and a pattern's binders do. Law vocabulary
def binds.group_stays(mode: Bind.Mode) -> Bool:
  match mode:
    case Bind.MSig{}:
      True{}
    case Bind.MLhs{_outer, _kind}:
      True{}
    case _other:
      False{}

# the mode the rest of a chain is read in after a leaf. After a statement's
# keyword comes its name. In a telescope an operator steps over the name it
# marks, a `:` starts the type, and in the type a `,` returns to the
# telescope and an `@` steps over the `x:` it binds. In a pattern a
# capitalized or dotted name with a group after it is a constructor, whose
# fields bind as pattern names; a `:` starts the pattern's type; `=` and `<-`
# start the term. In a term `@` and `&` step over the name they bind. Any
# other leaf leaves the mode as it was, a step-over ended. Law vocabulary
def binds.next(mode: Bind.Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Bind.Mode:
  match mode kk:
    case Bind.MHead{} Lex.TKey{}:
      Bind.MName{}
    case Bind.MTele{+kind} Lex.TOp{}:
      Bool.pick(Bind.Mode, Bind.plan.named(rest), Bind.MSkip{Bind.MTele{kind}}, Bind.MTele{kind})
    case Bind.MTele{kind} Lex.TColon{}:
      Bind.MTeleType{kind}
    case Bind.MTeleType{kind} Lex.TComma{}:
      Bind.MTele{kind}
    case Bind.MTeleType{+kind} Lex.TAll{}:
      Bool.pick(Bind.Mode, Bind.plan.typed(rest, False{}), Bind.MSkip{Bind.MTeleType{kind}}, Bind.MTeleType{kind})
    case Bind.MLhs{+outer, kind} Lex.TUpper{}:
      Bool.pick(Bind.Mode, Bind.plan.group(rest), Bind.MLhs{outer, Bind.KPat{}}, Bind.MLhs{outer, kind})
    case Bind.MLhs{+outer, kind} Lex.TDotted{}:
      Bool.pick(Bind.Mode, Bind.plan.group(rest), Bind.MLhs{outer, Bind.KPat{}}, Bind.MLhs{outer, kind})
    case Bind.MLhs{outer, _kind} Lex.TColon{}:
      Bind.MLhsType{outer}
    case Bind.MLhs{_outer, _kind} Lex.TEq{}:
      Bind.MTerm{}
    case Bind.MLhs{_outer, _kind} Lex.TBind{}:
      Bind.MTerm{}
    case Bind.MLhsType{_outer} Lex.TEq{}:
      Bind.MTerm{}
    case Bind.MLhsType{_outer} Lex.TBind{}:
      Bind.MTerm{}
    case Bind.MTerm{} Lex.TAll{}:
      Bool.pick(Bind.Mode, Bind.plan.typed(rest, True{}), Bind.MSkip{Bind.MTerm{}}, Bind.MTerm{})
    case Bind.MTerm{} Lex.TAmp{}:
      Bool.pick(Bind.Mode, Bind.plan.typed(rest, False{}), Bind.MSkip{Bind.MTerm{}}, Bind.MTerm{})
    case other _k:
      Bind.plan.skip(other)

# is a node a keyword leaf? Law vocabulary
def binds.is_key(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, _t, _l, _c}}:
      D1.kinds.among(k, [Lex.TKey{}])
    case _other:
      False{}

# LAW: the names a group binds stay bound after it exactly for a signature
# and a pattern
law plan_group_keeps:
  for mode: Bind.Mode
  {Bind.plan.gkeeps(mode) == binds.group_stays(mode) : Bool}

# LAW: after a leaf the rest is read in the mode binds.next gives
law plan_next_mode:
  for mode: Bind.Mode
  for kk: Lex.TokKind
  for +rest: Tree.Node
  {Bind.plan.lmode(mode, kk, rest) == binds.next(mode, kk, rest) : Bind.Mode}

# LAW: a statement's keyword is a keyword leaf, read by its kind and never
# its text
law declared_key_is_keyword:
  for nn: Tree.Node
  {Bind.declared.key(nn) == binds.is_key(nn) : Bool}

# LAW: a name is the one just put exactly when it heads the list
law again_at_head:
  for hh: String
  for rest: List<&2, String>
  for +name: String
  {Bind.push_name.again(hh <> rest, name) == String.eq(hh, name) : Bool}

# LAW: nothing was just put on an empty list
law again_needs_a_name:
  for acc: List<&2, String>
  for +name: String
  for e: {List.is_empty(&2, String, acc) == True{} : Bool}
  {Bind.push_name.again(acc, name) == False{} : Bool}

# LAW: an import gives the file its last word as an alias, in front of those
# before, unless that word is `Base` or `import` (an import with no `as`)
law aliases_take_last_word:
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  for +acc: List<&2, String>
  {Bind.aliases(Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, body}, rest}, acc)
    == Bind.aliases(rest,
      Bool.pick(List<&2, String>,
        Bool.or(String.eq(Bind.last_text(kids), "Base"), String.eq(Bind.last_text(kids), "import")), acc,
        Bind.last_text(kids) <> acc)) : List<&2, String>}

# LAW: in a declaration as written, spaces surround `->`
law spaced_arrow:
  for +tt: String
  for e: {String.eq(tt, "->") == True{} : Bool}
  {Bind.spaced(tt) == " -> " : String}

# LAW: a space follows `:` and `,`
law spaced_after_colon_and_comma:
  for +tt: String
  for e1: {String.eq(tt, "->") == False{} : Bool}
  for e2: {Bool.or(String.eq(tt, ":"), String.eq(tt, ",")) == True{} : Bool}
  {Bind.spaced(tt) == tt ++ " " : String}

# LAW: every other token is glued to its neighbours
law spaced_glues_the_rest:
  for +tt: String
  for e1: {String.eq(tt, "->") == False{} : Bool}
  for e2: {Bool.or(String.eq(tt, ":"), String.eq(tt, ",")) == False{} : Bool}
  {Bind.spaced(tt) == tt : String}
