import Base
import ../src/syntax/lex.bend as Lex
import ../src/rules/suspicious/concat.bend as Concat

# LAW: with nothing in place, the second maybe is the answer
law concat_either:
  for b: Maybe<&2, Lex.Tok>
  {Concat.either(None{}, b) == b : Maybe<&2, Lex.Tok>}
