# bolt/rules: the laws. Each rule is a pure function of the source it is
# handed, so its laws quantify over that source, never over one fixture.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
import ./suspicious/nat.bend as NatRule
import ./correctness/escape.bend as Esc
import ./correctness/put.bend as Put
import ./style/param.bend as Param
import ../../syntax/bind.bend as Bind
import ../paths.bend as Paths

# how many tokens are Nat literals of 1000 or more
def big_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TNum{}, +t, l, c}, rest}:
      +m = big_count(rest)
      Bool.pick(Nat, NatRule.big(t), 1n+m, m)
    case Con{h, rest}:
      big_count(rest)

# LAW: nat reports one finding for each Nat literal of 1000 or more, and none
# for any other token: a comment, a string, a U32 or a small Nat
# BOLT-RULE-U005
law nat_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, NatRule.check.go(toks, path)) == big_count(toks) : Nat}

# 1 when the Syms open with a digit (`0` included), else 0
def nul_lead(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SZero{}, t}:
      1n
    case Con{Esc.SDigit{d}, t}:
      1n
    case other:
      0n

# how many `\0`s a literal holds with a digit right after, its escapes read
# as Bend reads them: a backslash and the one char after it
def nul_count(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SSlash{}, Con{Esc.SZero{}, +rest}}:
      Nat.add(nul_lead(rest), nul_count(rest))
    case Con{Esc.SSlash{}, Con{e, rest}}:
      nul_count(rest)
    case Con{s, rest}:
      nul_count(rest)
    case Nil{}:
      0n

# how many such escapes the string and char literals among the tokens hold
def esc_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{Lex.Tok{Lex.TChar{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{h, rest}:
      esc_count(rest)
    case Nil{}:
      0n

# LAW: escape reports one finding for each `\0` then a digit in a literal,
# its escapes read a backslash and one char at a time, and none elsewhere in it
# BOLT-RULE-C006
law escape_scan_counts:
  for ss: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Esc.scan(ss, path, line, col)) == nul_count(ss) : Nat}

# LAW: escape reports exactly those escapes of the string and char literals,
# and nothing for any other token: a comment or code never has one
# BOLT-RULE-C006
law escape_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Esc.check.go(toks, path)) == esc_count(toks) : Nat}

# one char, and a capital
def one_upper(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{ch, Nil{}}:
      Char.is_upper(ch)
    case Con{ch, Con{d2, r}}:
      False{}
    case Nil{}:
      False{}

# a parameter binder shorter than 2 chars that is neither one capital (a type
# parameter) nor bare or typed `: Quant` (a quantity)
def too_short(kk: Bind.BindKind, +nm: String, +note: String) -> Bool:
  match kk:
    case Bind.KParam{}:
      Bool.and(Nat.is_lt(String.length(nm), 2n),
        Bool.not(Bool.or(one_upper(String.to_list(nm)),
          Bool.or(Bool.not(String.contains(note, ":")), String.ends_with(note, ": Quant")))))
    case other:
      False{}

# how many binders are parameters too short
def short_count(binds: List<&2, Bind.Bind>) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{+nm, line, col, kk, +note}, rest}:
      +m = short_count(rest)
      Bool.pick(Nat, too_short(kk, nm, note), 1n+m, m)

# LAW: over the binder list, param reports one finding for each parameter
# binder shorter than 2 chars that is neither one capital nor bare or typed
# `: Quant`, none for any other binder, and none at all in a PROOF.bend
# BOLT-RULE-S004
law param_counts:
  for binds: List<&2, Bind.Bind>
  for +path: String
  {List.length(&2, F.Finding, Param.check.on(binds, path))
    == Bool.pick(Nat, Paths.is_proof(path), 0n, short_count(binds)) : Nat}

# True when tt is `Map.put` and the tokens open with a `(` token
def put_open(+tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{Lex.TOpen{}, +o, l, c}, rest}:
      Bool.and(String.eq(tt, "Map.put"), String.eq(o, "("))
    case Con{h, rest}:
      False{}
    case Nil{}:
      False{}

# how many `Map.put` tokens have a `(` token right after them
def put_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TDotted{}, +t, l, c}, +rest}:
      +m = put_count(rest)
      Bool.pick(Nat, put_open(t, rest), 1n+m, m)
    case Con{h, rest}:
      put_count(rest)

# True when the first token's text is `Map.put`
def put_named(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      String.eq(t, "Map.put")
    case Nil{}:
      False{}

# True when some `def` keyword has a `Map.put` token right after it
def put_defined(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{Lex.TKey{}, +t, l, c}, +rest}:
      +m = put_defined(rest)
      Bool.or(Bool.and(String.eq(t, "def"), put_named(rest)), m)
    case Con{h, rest}:
      put_defined(rest)

# LAW: over the significant tokens, put reports one finding for each
# `Map.put` token with a `(` token right after it, and none at all when a
# `def` keyword has a `Map.put` token right after it
# BOLT-RULE-C004
law put_counts:
  for +toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Put.check.on(toks, path))
    == Bool.pick(Nat, put_defined(toks), 0n, put_count(toks)) : Nat}
