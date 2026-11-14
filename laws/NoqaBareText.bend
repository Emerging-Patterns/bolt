import Base
import ../src/noqa.bend as Noqa
import ./defs/NoqaSpacing.bend as D1

# LAW: a comment that is `#`, any number of spaces, `noqa`, a space and then
# any text is one bare mark, naming no code, whatever the text says
law noqa_bare_text:
  for line: U32
  for col: U32
  for len: U32
  for n: Nat
  for t: String
  {Noqa.mark.text(line, col, len, "#" ++ D1.nq.spaces(n) ++ "noqa " ++ t) == [Noqa.Mark{line, col, len, []}]
    : List<&2, Noqa.Mark>}
