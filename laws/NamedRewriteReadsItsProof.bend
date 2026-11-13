# A named rewrite `%h@e : P` (bend's explicit-motive form: h names the
# equation inside the motive P, and e proves it) reads e as a term. In a
# term a `%` with a name and then an `@` after it starts one: the
# binder steps over the name and the `@`, recording and using nothing, so
# what follows is read as any term is, and a name there is a use. Otherwise
# the `@` with `e :` after it would read as a dependent arrow's binder
# (`@e: A -> B`): e would bind a new name, and the e it means would look
# unused. The name h is the rewrite's own inside P: the binder gives it no
# binding site, so a use of it there resolves as a free name does. Only a
# `%` starts one: every other leaf is read by its kind as before
# (laws/BinderReadsBindingForms.bend), so an `@x:` with no `%` and name
# before it binds x, and a name and an `@` after any other operator are read
# as they were. Internal behavior of src/syntax/bind.bend, not interface.
#
# also rests on: laws/BinderReadsBindingForms.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ./defs/TokenKinds.bend as D1
import ./defs/Chains.bend as D2

# LAW: a chain starts a named rewrite's `h@` exactly when its first node is
# a name and its second an `@`
law rewrite_leads:
  for +rest: Tree.Node
  {Bind.plan.rewrites(rest)
    == Bool.and(D2.chains.leaf_of(D2.chains.front(rest), [Lex.TName{}]),
      D2.chains.leaf_of(D2.chains.front(D2.chains.after(rest)), [Lex.TAll{}])) : Bool}

# is the mode a term's? Law vocabulary: bolt never calls it
def rewrite.in_term(mode: Bind.Mode) -> Bool:
  match mode:
    case Bind.MTerm{}:
      True{}
    case _other:
      False{}

# LAW: in a term, after a `%` with a name and an `@` behind it, the next two
# leaves are stepped over and the term goes on
law percent_steps_over_name_and_at:
  for +rest: Tree.Node
  for e: {Bind.plan.rewrites(rest) == True{} : Bool}
  {Bind.plan.after(Bind.MTerm{}, Lex.TOp{}, "%", rest) == Bind.MSkip{Bind.MSkip{Bind.MTerm{}}} : Bind.Mode}

# LAW: in a term, a `%` with anything else behind it leaves the mode as it
# was
law percent_alone_stays:
  for +rest: Tree.Node
  for e: {Bind.plan.rewrites(rest) == False{} : Bool}
  {Bind.plan.after(Bind.MTerm{}, Lex.TOp{}, "%", rest) == Bind.MTerm{} : Bind.Mode}

# LAW: in a term, an operator that is no `%` leaves the mode as it was,
# whatever is behind it: `h @ k` after another operator is not a rewrite
law other_operator_stays:
  for +tt: String
  for +rest: Tree.Node
  for e: {String.eq(tt, "%") == False{} : Bool}
  {Bind.plan.after(Bind.MTerm{}, Lex.TOp{}, tt, rest) == Bind.MTerm{} : Bind.Mode}

# LAW: in a term, a leaf that is no operator is read by its kind, as
# laws/BinderReadsBindingForms.bend says, whatever it says
law other_kind_as_before:
  for kk: Lex.TokKind
  for +tt: String
  for +rest: Tree.Node
  for e: {D1.kinds.among(kk, [Lex.TOp{}]) == False{} : Bool}
  {Bind.plan.after(Bind.MTerm{}, kk, tt, rest) == Bind.plan.lmode(Bind.MTerm{}, kk, rest) : Bind.Mode}

# LAW: outside a term every leaf is read by its kind, as
# laws/BinderReadsBindingForms.bend says, whatever it says
law other_mode_as_before:
  for mode: Bind.Mode
  for kk: Lex.TokKind
  for +tt: String
  for +rest: Tree.Node
  for e: {rewrite.in_term(mode) == False{} : Bool}
  {Bind.plan.after(mode, kk, tt, rest) == Bind.plan.lmode(mode, kk, rest) : Bind.Mode}

# LAW: a leaf that is stepped over ends the step, whatever it is: the rest
# is read in the mode the step was to return to
law step_over_ends:
  for next: Bind.Mode
  for kk: Lex.TokKind
  for +tt: String
  for +rest: Tree.Node
  {Bind.plan.after(Bind.MSkip{next}, kk, tt, rest) == next : Bind.Mode}

# LAW: `%h@e :` in a term uses e, resolved against the names in scope, and
# binds nothing: the walk gives what a use of e alone gives, whatever the
# names, the positions, the scope and the output so far
law rewrite_uses_its_proof:
  for +ol: U32
  for +oc: U32
  for +ht: String
  for +hl: U32
  for +hc: U32
  for +at: String
  for +al: U32
  for +ac: U32
  for +et: String
  for +el: U32
  for +ec: U32
  for +ct: String
  for +cl: U32
  for +cc: U32
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  {Bind.walk(
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, "%", ol, oc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, ht, hl, hc}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, at, al, ac}},
          Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, et, el, ec}},
            Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, Tree.NNil{}}}}}},
    Bind.MTerm{}, env, ns, out) == Bind.use(et, el, ec, env, ns, out) : Bind.W}

# LAW: with no operator and name before it, `@e :` in a term still binds e:
# the walk records a binder at e and uses nothing
law arrow_still_binds:
  for +at: String
  for +al: U32
  for +ac: U32
  for +et: String
  for +el: U32
  for +ec: U32
  for +ct: String
  for +cl: U32
  for +cc: U32
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +scopes: List<&2, Bind.Scope>
  {Bind.walk(
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, at, al, ac}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, et, el, ec}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, Tree.NNil{}}}},
    Bind.MTerm{}, env, ns, Bind.Out{binds, uses, scopes})
    == Bind.W{Bind.Bind{et, el, ec, Bind.KTypeVar{}, ""} <> env,
      Bind.Out{Bind.Bind{et, el, ec, Bind.KTypeVar{}, ""} <> binds, uses, scopes}} : Bind.W}
