# the length of a string literal, as the laws of `prefix` read it
import Base
import ../../src/rules/suspicious/prefix.bend as Prefix

# A string literal's text is as the lexer keeps it, its quotes and escapes
# as written. Its length counts each char between the quotes once, and an
# escape once: a backslash and the char after it, or a `\u{..}` whole.
# Where a char is goes by the rule's own places (Prefix.Mode).

# what a char of a literal adds to its length, where the char is: one in its
# body, none for the closing quote, the opening quote, an escape's second
# char, a `\u{..}`'s braces and digits, or anything past the end
def prefix_add(mm: Prefix.Mode, +cc: Char) -> Nat:
  match mm:
    case Prefix.MOpen{}:
      0n
    case Prefix.MPlain{}:
      Bool.pick(Nat, U32.is_eq(Char.to_u32(cc), 34), 0n, 1n)
    case Prefix.MEsc{}:
      0n
    case Prefix.MUni{}:
      0n
    case Prefix.MDone{}:
      0n

# where the next char of a literal is, after this one: past the opening
# quote in the body, a backslash opening an escape, `u` after it a `\u{..}`
# that `}` closes, and a quote in the body ending it
def prefix_next(mm: Prefix.Mode, +cc: Char) -> Prefix.Mode:
  match mm:
    case Prefix.MOpen{}:
      Prefix.MPlain{}
    case Prefix.MPlain{}:
      Bool.pick(Prefix.Mode, U32.is_eq(Char.to_u32(cc), 92), Prefix.MEsc{},
        Bool.pick(Prefix.Mode, U32.is_eq(Char.to_u32(cc), 34), Prefix.MDone{}, Prefix.MPlain{}))
    case Prefix.MEsc{}:
      Bool.pick(Prefix.Mode, U32.is_eq(Char.to_u32(cc), 117), Prefix.MUni{}, Prefix.MPlain{})
    case Prefix.MUni{}:
      Bool.pick(Prefix.Mode, U32.is_eq(Char.to_u32(cc), 125), Prefix.MPlain{}, Prefix.MUni{})
    case Prefix.MDone{}:
      Prefix.MDone{}

# the length the rest of a literal's text adds, from where it is
def prefix_len_go(tt: String, +mm: Prefix.Mode) -> Nat:
  match tt:
    case SNil{}:
      0n
    case SCon{+cc, rest}:
      Nat.add(prefix_add(mm, cc), prefix_len_go(rest, prefix_next(mm, cc)))

# True when k is the literal's length, in decimal, then `n`
def prefix_fits(+kk: String, lit: String) -> Bool:
  String.eq(kk, Nat.show(prefix_len_go(lit, Prefix.MOpen{})) ++ "n")
