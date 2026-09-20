# rule escape: a string or char literal with `\0` then a digit, as in
# `"\033[1m"`. Bend's escapes are \n \t \r \0 \\ \' \" and \u{..}; it has no
# octal, so `\033` is NUL and then the chars "33" (nohzafk esc_bad: the bytes
# 00 33 33, not ESC), with no error. Write the code point, `\u{1B}`. Other
# unknown escapes (\x1b, \e) the checker rejects on its own.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../lazy/lazy.bend as Lazy

# an octal digit's value, or none
def octal(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 55)), Some{(x - 48 : U32)}, None{})

# keep the char when it is an octal digit, and those after it
def run.if(m: Maybe<&2, U32>, c: Char, rest: List<&2, Char>) -> List<&2, Char>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      c <> rest

# the octal digits (at most two) right after the `\0`, in order
def run(cs: List<&2, Char>, n: Nat) -> List<&2, Char>:
  match cs n:
    case Nil{} m:
      Nil{}
    case Con{c, t} 0n:
      Nil{}
    case Con{+c, t} 1n+p:
      run.if(octal(c), c, run(t, p))

# the digits' octal value
def value(cs: List<&2, Char>, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{Chr{+x}, t}:
      value(t, ((acc * 8) + (x - 48) : U32))

# a hex digit
def hexd(+n: U32) -> String:
  String.from_list([Chr{Bool.pick(U32, U32.is_lt(n, 10), (n + 48 : U32), (n + 55 : U32))}])

# a value under 256 in hex, without leading zeros
def hex(+n: U32) -> String:
  Bool.pick(String, U32.is_lt(n, 16), hexd(n), hexd((n / 16 : U32)) ++ hexd((n % 16 : U32)))

# the finding for `\0` at a column, the digits after it in ds
def finding(+ds: List<&2, Char>, +path: String, +line: U32, +col: U32) -> F.Finding:
  +digits = String.from_list(ds)
  Lazy.stop(F.Finding, List.is_empty(&2, Char, ds),
    F.Finding{path, line, col, 3, "escape", "\\0 then digits is NUL and the digits, not octal: write \\u{..}"},
    _u => F.Finding{path, line, col, (U32.from_nat(String.length(digits)) + 2 : U32), "escape",
      "\\0" ++ digits ++ " is NUL then \"" ++ digits ++ "\", not octal: write \\u{" ++ hex(value(ds, 0)) ++ "}"})

# after a `\0` at a column: a finding when a digit follows
def after(ds: List<&2, Char>, +path: String, +line: U32, +col: U32, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match ds:
    case Con{+d, t}:
      Lazy.stop(List<&2, F.Finding>, Bool.not(Char.is_digit(d)), more,
        _u => finding(run(d <> t, 2n), path, line, col) <> more)
    case Nil{}:
      more

# a literal's chars from a column; an escape is its backslash and one char
def scan(cs: List<&2, Char>, +path: String, +line: U32, +col: U32) -> List<&2, F.Finding>:
  match cs:
    case Con{'\\', Con{'0', +rest}}:
      after(rest, path, line, col, scan(rest, path, line, (col + 2 : U32)))
    case Con{'\\', Con{e, rest}}:
      scan(rest, path, line, (col + 2 : U32))
    case Con{c, rest}:
      scan(rest, path, line, (col + 1 : U32))
    case Nil{}:
      Nil{}

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      List.append(&2, F.Finding, scan(String.to_list(t), path, l, c), check.go(rest, path))
    case Con{Lex.Tok{Lex.TChar{}, t, l, c}, rest}:
      List.append(&2, F.Finding, scan(String.to_list(t), path, l, c), check.go(rest, path))
    case Con{h, rest}:
      check.go(rest, path)
    case Nil{}:
      Nil{}

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(toks, path)
