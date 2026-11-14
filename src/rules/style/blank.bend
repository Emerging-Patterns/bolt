# rule blank: a named String compared to the empty literal. Among the
# significant tokens (spaces, newlines and comments dropped): a dotted
# `String.eq`, `(`, a plain name x, `,`, the string literal `""` and `)`, or
# `String.eq`, `(`, `""`, `,`, x and `)`, right after one another. One
# finding, on the `String.eq` token, for each such call.
# The test asks whether x is empty; `String.is_empty(x)` (Base) says so and
# gives the same Bool for every x. It looks at one cell where String.eq
# builds a pair of the two strings to hand to a comparison (bend 2.0.40, 2M
# tests: the same on the native lane, 0.136 s against 0.094 s on JS when
# the test is x's only use, 0.29 s against 0.26 s when x is read again; no
# case slower). The rule's case is the plainer word, not the time.
# Only a plain name is read. Where the other argument is a call
# (`String.eq(lines(""), "")`), the `""` is as often the value a test
# expects as a question of emptiness, beside rows that expect `"a"` and
# `"\n"`: half of 30 such sites read by hand were that, so they are left
# alone. So is a literal of anything but nothing (`String.eq(x, " ")`), a
# qualified or aliased `eq`, and the shape written inside a string or a
# comment. A LAWS.bend or a PROOF.bend is exempt, and so is a `law` and a
# def that is a proof (`def f(x):`, or one that returns `-> {..}`) in any
# file, from its keyword to the next `def`, `type` or `import`
# (src/rules/suspicious/empty.bend's reading of one): a law states the test
# as it means it.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T
import ../suspicious/empty.bend as Empty

# the string literal `""`: a string token whose text is its two quotes
def lit(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TStr{}:
      String.eq(t, "\"\"")
    case other:
      False{}

# the name compared, when one of the two arguments is a plain name and the
# other `""`
def name(+ka: Lex.TokKind, +ta: String, +kb: Lex.TokKind, +tb: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.and(Empty.plain(ka), lit(kb, tb)), Some{ta},
    Bool.pick(Maybe<&2, String>, Bool.and(lit(ka, ta), Empty.plain(kb)), Some{tb}, None{}))

# the name, when the brackets and the comma are where they belong
def at.go(ok: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# the tokens after a `String.eq`: `(`, two arguments and `)`, one argument a
# plain name and the other `""`? Then the name
def at(toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Con{Lex.Tok{k1, t1, l1, c1}, Con{Lex.Tok{k2, t2, l2, c2}, Con{Lex.Tok{k3, t3, l3, c3},
      Con{Lex.Tok{k4, t4, l4, c4}, Con{Lex.Tok{k5, t5, l5, c5}, rest}}}}}:
      at.go(Bool.and(String.eq(Empty.code(k1, t1), "("), Bool.and(String.eq(Empty.code(k3, t3), ","),
        String.eq(Empty.code(k5, t5), ")"))), name(k2, t2, k4, t4))
    case other:
      None{}

# a dotted `String.eq`?
def named(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TDotted{}:
      String.eq(t, "String.eq")
    case other:
      False{}

# the test a token opens, if it is `String.eq`
def found.go(name: Bool, rest: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match name:
    case True{}:
      at(rest)
    case False{}:
      None{}

# the name a token's test compares, outside a law and a def that is a proof
def found(skip: Bool, k: Lex.TokKind, t: String, rest: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match skip:
    case True{}:
      None{}
    case False{}:
      found.go(named(k, t), rest)

# what a finding says: the test, and the word for it
def say(+x: String) -> String:
  "String.eq(" ++ x ++ ", \"\") asks whether " ++ x ++ " is empty; String.is_empty(" ++ x ++ ") says so."

# the finding a test makes, if any, before the rest
def hit(m: Maybe<&2, String>, +path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match m:
    case Some{x}:
      F.Finding{path, l, c, 9, "blank", say(x)} <> more
    case None{}:
      more

# every test among the tokens, in order; skip says whether the tokens so far
# sit in a law or a def that is a proof
def walk(toks: List<&2, Lex.Tok>, +path: String, skip: Bool) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      hit(found(sk, k, t, rest), path, l, c, walk(rest, path, sk))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path, False{}))

# the rule, told the file's role (src/role.bend): a law or proof file is
# skipped
def check.role(r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Role.is_law_file(r), [], _u => walk(T.sig(toks), path, False{}))
