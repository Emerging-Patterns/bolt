# proofs of laws/RulesReadSignaturesAndLiterals.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as Tokens
import ../laws/RulesReadSignaturesAndLiterals.bend as Laws
import ../laws/defs/Chains.bend as D2
import ./lemmas/BoolEmptiness.bend as M1

# a stop at the first True is the plain or
law rs.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def rs.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.has_colon_along_the_chain(h, rest):
  rs.or_else(Calls.kind.leaf(~Calls.kind.colon, h), Calls.has_colon(rest))

def Laws.has_colon_needs_a_chain(pp, e):
  match pp:
    case Tree.NCons{h, r}:
      Empty.absurd({Calls.has_colon(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.has_arrow_along_the_chain(h, rest):
  rs.or_else(Calls.kind.leaf(~Calls.kind.arrow, h), Calls.has_arrow(rest))

def Laws.has_arrow_needs_a_chain(pp, e):
  match pp:
    case Tree.NCons{h, r}:
      Empty.absurd({Calls.has_arrow(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.sign_is_first_operator(_h, _rest):
  {==}

def Laws.sign_needs_a_chain(pp, e):
  match pp:
    case Tree.NCons{h, r}:
      Empty.absurd({Calls.is_live.sign(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.returns_proof_needs_a_chain(sig, e):
  match sig:
    case Tree.NCons{h, r}:
      Empty.absurd({Calls.returns_proof(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.code_cuts_each_token(_h, _t):
  {==}

def Laws.nat_ends_in_n(cs, e):
  %Equal.sym(List<&2, Char>, cs, 'n' <> Nil{}, e) : {Tokens.nat_ok(_) == True{} : Bool}
  {==}

def Laws.nat_needs_chars(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Tokens.nat_ok(cs) == False{} : Bool}, M1.false_true(e))

def Laws.digits_need_chars(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Tokens.digits_ok(cs) == False{} : Bool}, M1.false_true(e))

def Laws.digits_of_one_char(_c):
  {==}
