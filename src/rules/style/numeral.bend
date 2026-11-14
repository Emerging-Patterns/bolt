# rule numeral: a `Nat` written as a conversion of a `U32` literal. Among
# the significant tokens (spaces, newlines and comments dropped): a dotted
# `U32.to_nat`, `(`, a number written in decimal digits alone, and `)`,
# right after one another. One finding, on the `U32.to_nat` token.
#
# `U32.to_nat(1024)` is the `Nat` literal `1024n`: the same value, in every
# place a term may stand, for every number a `U32` literal can hold (a
# `Nat` literal runs to `4294967295n` too). The literal says the number
# once and is what the reader looks for; and where a law's statement
# reaches the def, the checker keeps a literal as it is and has to run the
# conversion (bend 2.0.40, one comparison of two such numbers: 0.43 s and
# 164 MB written as literals, 0.88 s and 225 MB as conversions).
#
# Left alone: a conversion of anything but digits (`U32.to_nat(n)`,
# `U32.to_nat(1 + 2)`, `U32.to_nat(5n)`), a qualified or aliased name, and
# the shape written inside a string or a comment. A LAWS.bend or a
# PROOF.bend is exempt, and so is a `law` and a def that is a proof
# (`def f(x):`, or one that returns `-> {..}`) in any file, from its
# keyword to the next `def`, `type` or `import`
# (src/rules/suspicious/empty.bend's reading of one): a proof holds the
# shape a lemma was stated in, `U32.to_nat(0)` where the lemma says
# `U32.to_nat(x)`.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T
import ../suspicious/empty.bend as Empty

# are the chars all decimal digits?
def digits.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Lazy.and_then(Char.is_digit(c), _u => digits.all(rest))

# is the text one or more decimal digits and nothing else?
def digits(+t: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(t)), digits.all(String.to_list(t)))

# a number token written in digits alone: its text; "" for anything else
# (`5n`, `1.5`, a name)
def literal(k: Lex.TokKind, +t: String) -> String:
  match k:
    case Lex.TNum{}:
      Bool.pick(String, digits(t), t, "")
    case _other:
      ""

# the digits, when the brackets are where they belong; "" when not
def at.go(ok: Bool, ds: String) -> String:
  match ok:
    case True{}:
      ds
    case False{}:
      ""

# the tokens after a `U32.to_nat`: `(`, a number in digits and `)`? Then
# the digits, "" for any other shape
def at(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Con{Lex.Tok{k1, t1, _l1, _c1}, Con{Lex.Tok{k2, t2, _l2, _c2}, Con{Lex.Tok{k3, t3, _l3, _c3}, _rest}}}:
      at.go(Bool.and(String.eq(Empty.code(k1, t1), "("), String.eq(Empty.code(k3, t3), ")")), literal(k2, t2))
    case _other:
      ""

# a dotted `U32.to_nat`?
def named(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TDotted{}:
      String.eq(t, "U32.to_nat")
    case _other:
      False{}

# the digits of the conversion a token opens, if it is `U32.to_nat`
def found.go(name: Bool, rest: List<&2, Lex.Tok>) -> String:
  match name:
    case True{}:
      at(rest)
    case False{}:
      ""

# the digits of a token's conversion, outside a law and a def that is a
# proof
def found(skip: Bool, k: Lex.TokKind, t: String, rest: List<&2, Lex.Tok>) -> String:
  match skip:
    case True{}:
      ""
    case False{}:
      found.go(named(k, t), rest)

# what a finding says: the conversion, and the literal for it
def say(+ds: String) -> String:
  "U32.to_nat(" ++ ds ++ ") is the Nat literal " ++ ds ++ "n; write " ++ ds ++ "n."

# the finding on a `U32.to_nat`, over its ten chars
def cite(ds: String, path: String, l: U32, c: U32) -> F.Finding:
  F.Finding{path, l, c, 10, "numeral", say(ds)}

# a finding when there are digits, before the rest
def hit.go(none: Bool, ds: String, path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match none:
    case True{}:
      more
    case False{}:
      cite(ds, path, l, c) <> more

# the finding a conversion makes, if any, before the rest
def hit(+ds: String, path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  hit.go(String.is_empty(ds), ds, path, l, c, more)

# every such conversion among the tokens, in order; skip says whether the
# tokens so far sit in a law or a def that is a proof
def walk(toks: List<&2, Lex.Tok>, +path: String, skip: Bool) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      hit(found(sk, k, t, rest), path, l, c, walk(rest, path, sk))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, _text, toks, _tree, _bound, _items} = s
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path, False{}))

# the rule, told the file's role (src/role.bend): a law or proof file is
# skipped
def check.role(r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, _text, toks, _tree, _bound, _items} = s
  Lazy.stop(List<&2, F.Finding>, Role.is_law_file(r), [], _u => walk(T.sig(toks), path, False{}))
