import Base
import ../src/syntax/lex.bend as Lex
import ../src/rules/suspicious/concat.bend as Concat

# LAW: with nothing in place, the second maybe is the answer
law concat_either:
  for bb: Maybe<&2, Lex.Tok>
  {Concat.either(None{}, bb) == bb : Maybe<&2, Lex.Tok>}
