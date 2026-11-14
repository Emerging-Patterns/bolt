# rule negate: a `U32` or `Nat` comparison negated, where the opposite
# comparison has a word of its own. Among the significant tokens (spaces,
# newlines and comments dropped): a dotted `Bool.not`, `(`, a dotted
# comparison (`U32.is_eq`, `is_ne`, `is_lt`, `is_le`, `is_gt` or `is_ge`,
# or the same six of `Nat`), `(`, any tokens up to the `)` that closes that
# bracket, and `)` right after it. One finding, on the `Bool.not` token.
#
# Base has all six comparisons for both types, and each one negated is
# another of the six with the same Bool for every pair of arguments:
# `Bool.not(U32.is_eq(a, b))` is `U32.is_ne(a, b)`, and
# `Bool.not(Nat.is_lt(a, b))` is `Nat.is_ge(a, b)`. The plainer word says
# the test in one step, with one bracket fewer to match.
#
# Left alone: a `Bool.not` whose argument goes on past the comparison
# (`Bool.not(U32.is_eq(a, b) && c)`: the `)` that follows the comparison
# is not right after it); `F32`, where the negation of `is_lt` is not
# `is_ge` when either side is NaN; `Char` and `Cmp`, which have no `is_ne`
# to suggest; a qualified or aliased name; and the shape written inside a
# string or a comment. A LAWS.bend or a PROOF.bend is exempt, and so is a
# `law` and a def that is a proof (`def f(x):`, or one that returns
# `-> {..}`) in any file, from its keyword to the next `def`, `type` or
# `import` (src/rules/suspicious/empty.bend's reading of one): a law states
# the test as it means it.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T
import ../suspicious/empty.bend as Empty

# the opposite of one of the six comparisons, by its name after the type;
# "" for any other name
def opposite(+op: String) -> String:
  Bool.pick(String, String.eq(op, "is_eq"), "is_ne",
    Bool.pick(String, String.eq(op, "is_ne"), "is_eq",
      Bool.pick(String, String.eq(op, "is_lt"), "is_ge",
        Bool.pick(String, String.eq(op, "is_ge"), "is_lt",
          Bool.pick(String, String.eq(op, "is_gt"), "is_le", Bool.pick(String, String.eq(op, "is_le"), "is_gt", ""))))))

# the comparison of a type that the opposite of op names; "" when op is
# none of the six
def under(ty: String, op: String) -> String:
  +o = opposite(op)
  Bool.pick(String, String.is_empty(o), "", ty ++ "." ++ o)

# the word for a comparison negated: the opposite comparison of the same
# type, for `U32` and for `Nat`; "" for any other name
def word(+t: String) -> String:
  Bool.pick(String, String.starts_with(t, "U32."), under("U32", String.drop(t, 4n)),
    Bool.pick(String, String.starts_with(t, "Nat."), under("Nat", String.drop(t, 4n)), ""))

# the tokens after the bracket that closes a group, read from right inside
# it: d counts the brackets opened on the way and not yet closed, and done
# says the last token read was the closing one. None when the tokens run out
# first
def shut(toks: List<&2, Lex.Tok>, +d: Nat, done: Bool) -> Maybe<&2, List<&2, Lex.Tok>>:
  match toks done:
    case ts True{}:
      Some{ts}
    case Nil{} False{}:
      None{}
    case Con{Lex.Tok{+k, _t, _l, _c}, rest} False{}:
      shut(rest, Empty.close.depth(k, d), Empty.close.here(k, d))

# do the tokens open with `)`?
def ends.at(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k, t, _l, _c}, _rest}:
      String.eq(Empty.code(k, t), ")")

# does a `)` follow right after the bracket that closes the comparison?
def ends(m: Maybe<&2, List<&2, Lex.Tok>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{ts}:
      ends.at(ts)

# the comparison negated, when the brackets are where they belong; "" when
# not
def at.go(ok: Bool, w: String) -> String:
  match ok:
    case True{}:
      w
    case False{}:
      ""

# the tokens after a `Bool.not`: `(`, a dotted name, `(`, its arguments,
# `)` and `)`? Then the name's opposite, "" when it has none or the shape is
# another
def at(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Con{Lex.Tok{k1, t1, _l1, _c1}, Con{Lex.Tok{k2, t2, _l2, _c2}, Con{Lex.Tok{k3, t3, _l3, _c3}, rest}}}:
      at.go(Bool.and(String.eq(Empty.code(k1, t1), "("), Bool.and(Empty.dotted(k2),
        Bool.and(String.eq(Empty.code(k3, t3), "("), ends(shut(rest, 0n, False{}))))), word(t2))
    case _other:
      ""

# a dotted `Bool.not`?
def named(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TDotted{}:
      String.eq(t, "Bool.not")
    case _other:
      False{}

# the word for the test a token opens, if it is `Bool.not`
def found.go(name: Bool, rest: List<&2, Lex.Tok>) -> String:
  match name:
    case True{}:
      at(rest)
    case False{}:
      ""

# the word for a token's test, outside a law and a def that is a proof
def found(skip: Bool, k: Lex.TokKind, t: String, rest: List<&2, Lex.Tok>) -> String:
  match skip:
    case True{}:
      ""
    case False{}:
      found.go(named(k, t), rest)

# what a finding says: the word for the negated test
def say(+w: String) -> String:
  "Bool.not of this comparison is " ++ w ++ ", the same Bool for every pair of arguments; write " ++ w ++ "(..)."

# the finding on a `Bool.not`, over its eight chars
def cite(w: String, path: String, l: U32, c: U32) -> F.Finding:
  F.Finding{path, l, c, 8, "negate", say(w)}

# a finding when there is a word, before the rest
def hit.go(none: Bool, w: String, path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match none:
    case True{}:
      more
    case False{}:
      cite(w, path, l, c) <> more

# the finding a test makes, if any, before the rest
def hit(+w: String, path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  hit.go(String.is_empty(w), w, path, l, c, more)

# every negated comparison among the tokens, in order; skip says whether the
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
