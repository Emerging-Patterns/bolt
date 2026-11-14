# What the rules read off a def's signature and off a literal, where more
# than one rule reads it. A parameter is typed when a `:` stands among its
# own tokens, and a signature writes a return type when a `->` does; both are
# searched along the chain, never inside a group. A parameter is erased or a
# template when it opens with a `-` or a `~`. A Nat literal is digits and
# then one `n`; a U32 literal is one or more digits. Code, as a rule that
# must not read strings sees it, is the tokens with each string literal cut
# to its opening quote.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as Tokens
import ./defs/Chains.bend as D2

# LAW: a chain holds a top-level `:` when its first node is one or the rest
# of the chain holds one
law has_colon_along_the_chain:
  for h: Tree.Node
  for rest: Tree.Node
  {Calls.has_colon(Tree.NCons{h, rest}) == Bool.or(Calls.kind.leaf(~Calls.kind.colon, h), Calls.has_colon(rest))
    : Bool}

# LAW: what is no chain holds no `:`
law has_colon_needs_a_chain:
  for pp: Tree.Node
  for e: {D2.chains.is_cons(pp) == False{} : Bool}
  {Calls.has_colon(pp) == False{} : Bool}

# LAW: a chain holds a top-level `->` when its first node is one or the rest
# of the chain holds one
law has_arrow_along_the_chain:
  for h: Tree.Node
  for rest: Tree.Node
  {Calls.has_arrow(Tree.NCons{h, rest}) == Bool.or(Calls.kind.leaf(~Calls.kind.arrow, h), Calls.has_arrow(rest))
    : Bool}

# LAW: what is no chain holds no `->`
law has_arrow_needs_a_chain:
  for pp: Tree.Node
  for e: {D2.chains.is_cons(pp) == False{} : Bool}
  {Calls.has_arrow(pp) == False{} : Bool}

# LAW: a parameter is marked erased or a template when its first node is an
# operator whose text is `-` or `~`
law sign_is_first_operator:
  for +h: Tree.Node
  for rest: Tree.Node
  {Calls.is_live.sign(Tree.NCons{h, rest})
    == Bool.and(Calls.kind.leaf(~Calls.kind.oper, h),
      Bool.or(String.eq(Calls.leaf.text(h), "-"), String.eq(Calls.leaf.text(h), "~"))) : Bool}

# LAW: what is no chain carries no mark
law sign_needs_a_chain:
  for pp: Tree.Node
  for e: {D2.chains.is_cons(pp) == False{} : Bool}
  {Calls.is_live.sign(pp) == False{} : Bool}

# LAW: what is no chain returns no proof
law returns_proof_needs_a_chain:
  for sig: Tree.Node
  for e: {D2.chains.is_cons(sig) == False{} : Bool}
  {Calls.returns_proof(sig) == False{} : Bool}

# LAW: each token is cut on its own, in order
law code_cuts_each_token:
  for h: Lex.Tok
  for t: List<&2, Lex.Tok>
  {Tokens.code.toks(h <> t) == Tokens.code.tok(h) <> Tokens.code.toks(t) : List<&2, Lex.Tok>}

# LAW: a string literal is cut to its first char, its kind and place kept
law code_cuts_a_string:
  for +kk: Lex.TokKind
  for +tt: String
  for ll: U32
  for cc: U32
  for e: {Lex.is_str(kk) == True{} : Bool}
  {Tokens.code.tok(Lex.Tok{kk, tt, ll, cc}) == Lex.Tok{kk, Tokens.code.cut(tt), ll, cc} : Lex.Tok}

# LAW: any other token is as it was
law code_keeps_other_tokens:
  for +kk: Lex.TokKind
  for +tt: String
  for ll: U32
  for cc: U32
  for e: {Lex.is_str(kk) == False{} : Bool}
  {Tokens.code.tok(Lex.Tok{kk, tt, ll, cc}) == Lex.Tok{kk, tt, ll, cc} : Lex.Tok}

# LAW: a Nat literal's value is its digits read as a U32: the text without
# its final `n`
law nat_value_reads_the_digits:
  for +tt: String
  for e: {Tokens.nat_ok(String.to_list(tt)) == True{} : Bool}
  {Tokens.nat_value(tt) == U32.read(Tokens.stem(tt)) : Maybe<&2, U32>}

# LAW: a text that is no Nat literal has no value
law nat_value_needs_a_literal:
  for +tt: String
  for e: {Tokens.nat_ok(String.to_list(tt)) == False{} : Bool}
  {Tokens.nat_value(tt) == None{} : Maybe<&2, U32>}

# LAW: the chars `n` alone end a Nat literal
law nat_ends_in_n:
  for cs: List<&2, Char>
  for e: {cs == 'n' <> Nil{} : List<&2, Char>}
  {Tokens.nat_ok(cs) == True{} : Bool}

# LAW: no chars are no Nat literal
law nat_needs_chars:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Tokens.nat_ok(cs) == False{} : Bool}

# LAW: no chars are no U32 literal
law digits_need_chars:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Tokens.digits_ok(cs) == False{} : Bool}

# LAW: one char is a U32 literal exactly when it is a digit
law digits_of_one_char:
  for +c: Char
  {Tokens.digits_ok(c <> Nil{}) == Char.is_digit(c) : Bool}
