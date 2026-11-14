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

def Laws.has_colon_needs_a_chain(p, e):
  match p:
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

def Laws.has_arrow_needs_a_chain(p, e):
  match p:
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

def Laws.sign_needs_a_chain(p, e):
  match p:
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

def Laws.code_cuts_a_string(k, t, l, c, e):
  %Equal.sym(Bool, Lex.is_str(k), True{}, e) :
    {Lex.Tok{k, Bool.pick(String, _, Tokens.code.cut(t), t), l, c} == Lex.Tok{k, Tokens.code.cut(t), l, c}
      : Lex.Tok}
  {==}

def Laws.code_keeps_other_tokens(k, t, l, c, e):
  %Equal.sym(Bool, Lex.is_str(k), False{}, e) :
    {Lex.Tok{k, Bool.pick(String, _, Tokens.code.cut(t), t), l, c} == Lex.Tok{k, t, l, c} : Lex.Tok}
  {==}

def Laws.nat_value_reads_the_digits(t, e):
  %Equal.sym(Bool, Tokens.nat_ok(String.to_list(t)), True{}, e) :
    {Bool.pick(Maybe<&2, U32>, _, U32.read(Tokens.stem(t)), None{}) == U32.read(Tokens.stem(t)) : Maybe<&2, U32>}
  {==}

def Laws.nat_value_needs_a_literal(t, e):
  %Equal.sym(Bool, Tokens.nat_ok(String.to_list(t)), False{}, e) :
    {Bool.pick(Maybe<&2, U32>, _, U32.read(Tokens.stem(t)), None{}) == None{} : Maybe<&2, U32>}
  {==}
