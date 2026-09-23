# syntax: the laws. Each quantifies over every source, never one fixture.
import Base
import ./lex.bend as Lex

# LAW: the tokens' texts spell the source back, whatever the source is
# BOLT-SYN-1
law lossless:
  for +s: String
  {Lex.text(Lex.tokens(s)) == s : String}
