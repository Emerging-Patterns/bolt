# `space` reports exactly trailing whitespace or a tab on any line, string
# literals and `#|` lines included, or a line over 120 columns with string
# literals counted as two, comments at full width, and `#|` lines and import
# lines not counted.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/rules/style/space.bend as Space
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/laws/unsafe.bend as Unsafe
import ./defs/Unsafe.bend as D1

# True when the line's last char is whitespace
def ends_space(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, Nil{}}:
      Char.is_space(c)
    case Con{c, t}:
      ends_space(t)

# True when a tab is among the chars
def tabbed(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Bool.or(Char.is_eq(c, '\t'), tabbed(t))

# how many lines end in whitespace or hold a tab, one each
def space_count(lines: List<&2, String>) -> Nat:
  match lines:
    case Nil{}:
      0n
    case Con{+line, rest}:
      +m = space_count(rest)
      Bool.pick(Nat, Bool.or(ends_space(String.to_list(line)), tabbed(String.to_list(line))), 1n+m, m)

# LAW: over the text's lines, space reports one finding for each line that
# ends in whitespace or holds a tab, anywhere in it (a string literal or a
# `#|` line included), and none for any other line
law space_line_counts:
  for lines: List<&2, String>
  for +path: String
  for +nn: U32
  {List.length(&2, F.Finding, Space.check.go(lines, path, nn)) == space_count(lines) : Nat}

# how many lines are over 120 columns, the first already acc wide; a newline
# token closes a line
def wide_count(toks: List<&2, Lex.Tok>, +acc: U32) -> Nat:
  match toks:
    case Nil{}:
      D1.over(acc, 0n)
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      D1.over(acc, wide_count(rest, 0))
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      wide_count(rest, (acc + D1.share(k, t) : U32))

# LAW: over the tokens, space reports one finding for each line over 120
# columns, a string literal counted as two, a comment at its full width and a
# `#|` comment as nothing, and none for any other line
law space_width_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  for +nn: U32
  for +acc: U32
  {List.length(&2, F.Finding, Space.widths(toks, path, nn, acc)) == wide_count(toks, acc) : Nat}

# LAW: space reports exactly those two: the lines of the text with trailing
# whitespace or a tab, then the lines of the tokens over 120 columns, an
# import line counting as nothing
law space_counts:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Space.check(Src.Src{path, text, toks, tree, bound, items}))
    == Nat.add(space_count(String.lines(text)), wide_count(Space.unimported(toks, True{}, False{}), 0)) : Nat}
