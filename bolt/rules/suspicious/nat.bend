# rule nat: a Nat literal (a number ending in `n`) of 1000 or more. Nat is
# unary: `4294967295n` as an "infinity" or as fuel is four billion cells that
# eat all memory (rootagi, AppSprout, gavel), and a big literal overflows the
# checker's stack. Count in U32, or build the Nat at run time with
# U32.to_nat when it must be one.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../tokens.bend as T

# the chars without their leading zeros
def unpad(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{'0', t}:
      unpad(t)
    case other:
      other

# is the text a Nat literal (digits, then `n`) of four or more digits past its zeros?
def big(+tt: String) -> Bool:
  +cs = String.to_list(tt)
  Bool.and(T.nat_ok(cs), Nat.is_gt(List.length(&2, Char, unpad(cs)), 4n))

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TNum{}, +t, l, c}, rest}:
      +more = check.go(rest, path)
      +k = T.stem(t)
      Bool.pick(List<&2, F.Finding>, big(t),
        F.Finding{path, l, c, T.width(t), "nat",
          t ++ " is " ++ k ++ " unary cells; use U32 (or U32.to_nat at run time) for big counts"} <> more,
        more)
    case Con{h, rest}:
      check.go(rest, path)
    case Nil{}:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(toks, path)
