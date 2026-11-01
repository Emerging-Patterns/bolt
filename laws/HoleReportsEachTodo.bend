# `hole` reports exactly a TODO hole bend counts, a `?` then `TODO` with only
# spaces, newlines or comments between, outside a LAWS.bend, and nothing else.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/hole.bend as Hole
import ../src/paths.bend as Paths

# True when the first token past spaces, newlines and comments is `TODO`
def todo_next(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{Lex.TSpace{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TComment{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TUpper{}, +t, l, c}, rest}:
      String.eq(t, "TODO")
    case other:
      False{}

# how many `?` tokens have `TODO` next past spaces, newlines and comments
def hole_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TOp{}, +q, l, c}, +rest}:
      +m = hole_count(rest)
      Bool.pick(Nat, Bool.and(String.eq(q, "?"), todo_next(rest)), 1n+m, m)
    case Con{h, rest}:
      hole_count(rest)

# LAW: hole reports one finding for each `?` token with `TODO` next past
# spaces, newlines and comments, none for any other token, and none at all in
# a LAWS.bend
law hole_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Hole.check.on(toks, path))
    == Bool.pick(Nat, Paths.is_laws(path), 0n, hole_count(toks)) : Nat}
