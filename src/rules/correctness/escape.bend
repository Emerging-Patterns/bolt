# rule escape: a string or char literal with `\0` then a digit, as in
# `"\033[1m"`. Bend's escapes are \n \t \r \0 \\ \' \" and \u{..}; it has no
# octal, so `\033` is NUL and then the chars "33" (nohzafk esc_bad: the bytes
# 00 33 33, not ESC), with no error. Write the code point, `\u{1B}`. Other
# unknown escapes (\x1b, \e) the checker rejects on its own.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../lazy/lazy.bend as Lazy

# a literal's char as the rule reads it: a backslash, a `0`, another digit,
# or anything else. Read once, so the scan below matches constructors, not
# char literals.
type Sym is Data:
  SSlash{}
  SZero{}
  SDigit{c: Char}
  SOther{c: Char}

# a char as a Sym
def sym(cc: Char) -> Sym:
  match cc:
    case Chr{+x}:
      Bool.pick(Sym, U32.is_eq(x, 92), SSlash{},
        Bool.pick(Sym, U32.is_eq(x, 48), SZero{},
          Bool.pick(Sym, Bool.and(U32.is_ge(x, 49), U32.is_le(x, 57)), SDigit{Chr{x}}, SOther{Chr{x}})))

# a literal's chars as Syms
def syms(cs: List<&2, Char>) -> List<&2, Sym>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      sym(c) <> syms(t)

# the Sym's char when it is an octal digit
def octal(ss: Sym) -> Maybe<&2, Char>:
  match ss:
    case SZero{}:
      Some{'0'}
    case SDigit{Chr{+x}}:
      Bool.pick(Maybe<&2, Char>, U32.is_le(x, 55), Some{Chr{x}}, None{})
    case other:
      None{}

# keep the octal digit, and those after it
def run.if(mm: Maybe<&2, Char>, rest: List<&2, Char>) -> List<&2, Char>:
  match mm:
    case None{}:
      Nil{}
    case Some{c}:
      c <> rest

# the octal digits (at most two) right after the `\0`, in order
def run(ss: List<&2, Sym>, nn: Nat) -> List<&2, Char>:
  match ss nn:
    case Nil{} m:
      Nil{}
    case Con{s, t} 0n:
      Nil{}
    case Con{s, t} 1n+p:
      run.if(octal(s), run(t, p))

# the digits' octal value
def value(cs: List<&2, Char>, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{Chr{+x}, t}:
      value(t, ((acc * 8) + (x - 48) : U32))

# a hex digit
def hexd(+nn: U32) -> String:
  String.from_list([Chr{Bool.pick(U32, U32.is_lt(nn, 10), (nn + 48 : U32), (nn + 55 : U32))}])

# a value under 256 in hex, without leading zeros
def hex(+nn: U32) -> String:
  Bool.pick(String, U32.is_lt(nn, 16), hexd(nn), hexd((nn / 16 : U32)) ++ hexd((nn % 16 : U32)))

# the finding for `\0` at a column, the digits after it in ds
def finding(+ds: List<&2, Char>, +path: String, +line: U32, +col: U32) -> F.Finding:
  +digits = String.from_list(ds)
  Lazy.stop(F.Finding, List.is_empty(&2, Char, ds),
    F.Finding{path, line, col, 3, "escape",
      "\\0 followed by digits is a NUL character and then those digits, not an octal escape; write \\u{..} instead."},
    _u => F.Finding{path, line, col, (U32.from_nat(String.length(digits)) + 2 : U32), "escape",
      "\\0" ++ digits ++ " is a NUL character followed by \"" ++ digits ++ "\", not an octal escape; write \\u{" ++ hex(value(ds, 0)) ++ "}."})

# after a `\0` at a column: a finding when a digit follows
def after(ss: List<&2, Sym>, +path: String, +line: U32, +col: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match ss:
    case Con{SZero{}, t}:
      finding(run(SZero{} <> t, 2n), path, line, col) <> more
    case Con{SDigit{d}, t}:
      finding(run(SDigit{d} <> t, 2n), path, line, col) <> more
    case other:
      more

# a literal's Syms from a column; an escape is its backslash and one char
def scan(ss: List<&2, Sym>, +path: String, +line: U32, +col: U32) -> List<&2, F.Finding>:
  match ss:
    case Con{SSlash{}, Con{SZero{}, +rest}}:
      after(rest, path, line, col, scan(rest, path, line, (col + 2 : U32)))
    case Con{SSlash{}, Con{e, rest}}:
      scan(rest, path, line, (col + 2 : U32))
    case Con{s, rest}:
      scan(rest, path, line, (col + 1 : U32))
    case Nil{}:
      Nil{}

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      List.append(&2, F.Finding, scan(syms(String.to_list(t)), path, l, c), check.go(rest, path))
    case Con{Lex.Tok{Lex.TChar{}, t, l, c}, rest}:
      List.append(&2, F.Finding, scan(syms(String.to_list(t)), path, l, c), check.go(rest, path))
    case Con{h, rest}:
      check.go(rest, path)
    case Nil{}:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(toks, path)
