# `Lex.text(Lex.tokens(s)) == s` for every `s`.
import Base
import ../src/syntax/lex.bend as Lex

# LAW: the tokens' texts spell the source back, whatever the source is
law lossless:
  for +s: String
  {Lex.text(Lex.tokens(s)) == s : String}
