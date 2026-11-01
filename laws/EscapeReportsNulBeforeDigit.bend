# `escape` reports exactly one finding for each `\0` followed by a digit in a
# string or char literal, its escapes read as a backslash and the one char
# after it, and none for anything else.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/escape.bend as Esc

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
law escape_scan_counts:
  for ss: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Esc.scan(ss, path, line, col)) == nul_count(ss) : Nat}

# LAW: escape reports exactly those escapes of the string and char literals,
# and nothing for any other token: a comment or code never has one
law escape_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Esc.check.go(toks, path)) == esc_count(toks) : Nat}
