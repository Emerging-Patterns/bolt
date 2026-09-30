# src/rchars: a buffer of chars read one at a time and consed on the front
# (the last read first) as the String it spells, in one pass: each char goes
# onto the String built so far, with no reversed list in between (the shape
# `fromrev`, U016, reports). Pure.
import Base

# the buffer's chars, first read first, then acc
def onto(buf: List<&2, Char>, acc: String) -> String:
  match buf:
    case Nil{}:
      acc
    case Con{h, t}:
      onto(t, SCon{h, acc})

# the buffer's chars, first read first
def text(buf: List<&2, Char>) -> String:
  onto(buf, SNil{})
