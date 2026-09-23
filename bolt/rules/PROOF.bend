# bolt/rules: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
import ./tokens.bend as T
import ./suspicious/nat.bend as NatRule
import ./LAWS.bend as Laws

# a finding in front when b holds adds one to the count
law nat.pick:
  for b: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, x <> more, more)) == Bool.pick(Nat, b, 1n+m, m)
    : Nat}

def nat.pick(b, _x, more, m, ih):
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# one token onto a list the law holds for
law nat.step:
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, NatRule.check.go(rest, path)) == Laws.big_count(rest) : Nat}
  {List.length(&2, F.Finding, NatRule.check.go(Lex.Tok{kk, t, l, c} <> rest, path))
    == Laws.big_count(Lex.Tok{kk, t, l, c} <> rest) : Nat}

def nat.step(kk, t, l, c, rest, path, ih):
  match kk:
    case Lex.TNum{}:
      nat.pick(NatRule.big(t), F.Finding{path, l, c, T.width(t), "nat",
        t ++ " is " ++ T.stem(t) ++ " unary cells; Nat literals of 1000 or more are unary, so use U32, or U32.to_nat at run time."},
        NatRule.check.go(rest, path), Laws.big_count(rest), ih)
    case Lex.TName{}:
      ih
    case Lex.TUpper{}:
      ih
    case Lex.TDotted{}:
      ih
    case Lex.TWild{}:
      ih
    case Lex.TKey{}:
      ih
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
      ih
    case Lex.TComment{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      ih
    case Lex.TColon{}:
      ih
    case Lex.TEq{}:
      ih
    case Lex.TBind{}:
      ih
    case Lex.TArrow{}:
      ih
    case Lex.TLam{}:
      ih
    case Lex.TAll{}:
      ih
    case Lex.TAmp{}:
      ih
    case Lex.TOpen{}:
      ih
    case Lex.TClose{}:
      ih
    case Lex.TComma{}:
      ih

def Laws.nat_counts(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      nat.step(kk, t, l, c, rest, path, Laws.nat_counts(rest, path))
