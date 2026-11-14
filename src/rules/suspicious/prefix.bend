# rule prefix: a String.take compared to a literal of its length:
# `String.eq(String.take(s, k), "..")` or `String.eq("..", String.take(s,
# k))`. Among the significant tokens (spaces, newlines and comments dropped):
# a dotted name `String.eq`, `(`, `String.take` and `(`, then the take's
# first argument s, any tokens up to the first comma outside the brackets
# they open (a call such as `String.drop(m, 4n)` is one argument), then a
# Nat literal k, `)`, `,`, a string literal and `)`; or the dotted name
# `String.eq`, `(`, the string literal, `,`, `String.take`, `(`, s, the
# comma, k, `)` and `)`. Only when k's text is the literal's length (an
# escape, `\n` or `\u{1B}`, one char) written in decimal with an `n`, as
# `4n` for `"ERR "`. A bracket that closes the take before any such comma
# ends the scan with no finding. One finding, on the `String.eq` token, for
# each such run, and nothing else: a take of another length is another bug.
# String.take copies k chars into a new String only to compare them;
# `String.starts_with(s, "ERR ")` (Base) walks s in place and gives the same
# answer for every s, False when s is shorter, s any expression. A LAWS.bend
# or a PROOF.bend, which never runs, is exempt. A comment is never read, and
# a string literal is one token, so the shape written inside either is not
# the shape.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# where the length of a string literal's text is: before its opening
# quote, in plain text, just after a backslash, inside a `\u{..}`, or past
# its closing quote
type Mode is Data:
  MOpen{}
  MPlain{}
  MEsc{}
  MUni{}
  MDone{}

# is the char the code point?
def is_cp(+c: Char, +x: U32) -> Bool:
  U32.is_eq(Char.to_u32(c), x)

# what the char adds to the length: one in plain text, but not the closing
# quote; nothing anywhere else
def len.add(m: Mode, +c: Char) -> Nat:
  match m:
    case MPlain{}:
      Bool.pick(Nat, is_cp(c, 34), 0n, 1n)
    case other:
      0n

# where the char leaves the length: a backslash starts an escape, a quote
# closes the literal, `u` after a backslash opens a `\u{..}` and `}` closes
# it
def len.next(m: Mode, +c: Char) -> Mode:
  match m:
    case MOpen{}:
      MPlain{}
    case MPlain{}:
      Bool.pick(Mode, is_cp(c, 92), MEsc{}, Bool.pick(Mode, is_cp(c, 34), MDone{}, MPlain{}))
    case MEsc{}:
      Bool.pick(Mode, is_cp(c, 117), MUni{}, MPlain{})
    case MUni{}:
      Bool.pick(Mode, is_cp(c, 125), MPlain{}, MUni{})
    case MDone{}:
      MDone{}

# the length of the rest of a literal's text, from where it is
def len.go(t: String, +m: Mode) -> Nat:
  match t:
    case SNil{}:
      0n
    case SCon{+c, rest}:
      Nat.add(len.add(m, c), len.go(rest, len.next(m, c)))

# the length of a string literal, its text as the lexer keeps it (quotes
# and escapes as written): each escape one char
def len(t: String) -> Nat:
  len.go(t, MOpen{})

# is the Nat literal's text the literal's length?
def fits(+k: String, lit: String) -> Bool:
  String.eq(k, Nat.show(len(lit)) ++ "n")

# what the finding says: the take, and the starts_with that replaces it
def say(+s: String, +k: String, +lit: String) -> String:
  "String.eq(String.take(" ++ s ++ ", " ++ k ++ "), " ++ lit ++ ") copies " ++ k
    ++ " chars only to compare them; String.starts_with(" ++ s ++ ", " ++ lit ++ ") gives the same answer in place."

# where the scan of a take's first argument stands: inside it at a depth of
# brackets it opened, just past the comma that ends it, or at the bracket
# that closes the take before any such comma
type Skip is Data:
  SGo{depth: Nat}
  SComma{}
  SClose{}

# the argument as the finding writes it, and the tokens after its comma
type Arg is Data:
  Arg{text: String, rest: List<&2, Lex.Tok>}

# a comma at the depth: the argument's end at depth zero, else inside it
def skip.comma(d: Nat) -> Skip:
  match d:
    case 0n:
      SComma{}
    case 1n+p:
      SGo{1n+p}

# a closing bracket at the depth: the take's own at depth zero, else one
# bracket the argument opened
def skip.close(d: Nat) -> Skip:
  match d:
    case 0n:
      SClose{}
    case 1n+p:
      SGo{p}

# where a token of the kind leaves the scan at the depth
def skip.step(k: Lex.TokKind, d: Nat) -> Skip:
  match k:
    case Lex.TComma{}:
      skip.comma(d)
    case Lex.TOpen{}:
      SGo{1n+d}
    case Lex.TClose{}:
      skip.close(d)
    case other:
      SGo{d}

# a token as the finding writes it: a comma with a space after it, an
# operator with one on each side
def piece(k: Lex.TokKind, +t: String) -> String:
  match k:
    case Lex.TComma{}:
      ", "
    case Lex.TOp{}:
      " " ++ t ++ " "
    case other:
      t

# what a token adds to the argument's text, given where it leaves the scan:
# nothing for the comma that ends the argument
def skip.piece(sk: Skip, k: Lex.TokKind, +t: String) -> String:
  match sk:
    case SComma{}:
      ""
    case other:
      piece(k, t)

# the take's first argument, scanned from where the scan stands: what it
# says (acc: its pieces so far, last first) and the tokens after the comma
# that ends it; none when the take
# closes first or the tokens run out
def skip(toks: List<&2, Lex.Tok>, sk: Skip, +acc: List<&2, String>) -> Maybe<&2, Arg>:
  match toks:
    case Nil{}:
      None{}
    case Con{Lex.Tok{+k, +t, l, c}, rest}:
      match sk:
        case SComma{}:
          Some{Arg{String.join(List.reverse(&2, String, acc), ""), Lex.Tok{k, t, l, c} <> rest}}
        case SClose{}:
          None{}
        case SGo{d}:
          +nx = skip.step(k, d)
          skip(rest, nx, skip.piece(nx, k, t) <> acc)

# a dotted name: what `String.eq` is
def dotted(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# after the argument's comma, k, `)`, `,`, a string literal and `)`: is k
# the literal's length?
def tail_a.ok(+k: String, +t7: String, +t8: String, k9: Lex.TokKind, +t9: String, +t10: String) -> Bool:
  Bool.and(String.eq(t7, ")"), Bool.and(String.eq(t8, ","), Bool.and(Lex.is_str(k9),
    Bool.and(String.eq(t10, ")"), fits(k, t9)))))

# the take-first shape's end, after the argument: what the finding says
def tail_a(ma: Maybe<&2, Arg>) -> Maybe<&2, String>:
  match ma:
    case None{}:
      None{}
    case Some{Arg{+s, r}}:
      match r:
        case Con{Lex.Tok{k6, +t6, l6, c6}, Con{Lex.Tok{k7, +t7, l7, c7}, Con{Lex.Tok{k8, +t8, l8, c8},
          Con{Lex.Tok{k9, +t9, l9, c9}, Con{Lex.Tok{k10, +t10, l10, c10}, rest}}}}}:
          Bool.pick(Maybe<&2, String>, tail_a.ok(t6, t7, t8, k9, t9, t10), Some{say(s, t6, t9)}, None{})
        case other:
          None{}

# after the argument's comma, k, `)` and `)`: is k the literal's length?
def tail_b.ok(+k: String, +t9: String, +t10: String, +lit: String) -> Bool:
  Bool.and(String.eq(t9, ")"), Bool.and(String.eq(t10, ")"), fits(k, lit)))

# the literal-first shape's end, after the argument: what the finding says
def tail_b(ma: Maybe<&2, Arg>, +lit: String) -> Maybe<&2, String>:
  match ma:
    case None{}:
      None{}
    case Some{Arg{+s, r}}:
      match r:
        case Con{Lex.Tok{k8, +t8, l8, c8}, Con{Lex.Tok{k9, +t9, l9, c9}, Con{Lex.Tok{k10, +t10, l10, c10}, rest}}}:
          Bool.pick(Maybe<&2, String>, tail_b.ok(t8, t9, t10, lit), Some{say(s, t8, lit)}, None{})
        case other:
          None{}

# a dotted `String.eq`, `(`, `String.take` and `(`?
def head_a(k0: Lex.TokKind, +t0: String, +t1: String, +t2: String, +t3: String) -> Bool:
  Bool.and(dotted(k0), Bool.and(String.eq(t0, "String.eq"), Bool.and(String.eq(t1, "("),
    Bool.and(String.eq(t3, "("), String.eq(t2, "String.take")))))

# the take-first shape, its head read: the end, after the argument
def at_a.go(ok: Bool, r3: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      tail_a(skip(r3, SGo{0n}, []))
    case False{}:
      None{}

# a token of kind k0 and text t0, then these: the take-first shape?
def at_a(k0: Lex.TokKind, +t0: String, toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Con{Lex.Tok{k1, +t1, l1, c1}, Con{Lex.Tok{k2, +t2, l2, c2}, Con{Lex.Tok{k3, +t3, l3, c3}, r3}}}:
      at_a.go(head_a(k0, t0, t1, t2, t3), r3)
    case other:
      None{}

# a dotted `String.eq`, `(`, a string literal, `,`, `String.take` and `(`?
def head_b(k0: Lex.TokKind, +t0: String, +t1: String, k2: Lex.TokKind, +t3: String, +t4: String, +t5: String) -> Bool:
  Bool.and(dotted(k0), Bool.and(String.eq(t0, "String.eq"), Bool.and(String.eq(t1, "("), Bool.and(Lex.is_str(k2),
    Bool.and(String.eq(t3, ","), Bool.and(String.eq(t4, "String.take"), String.eq(t5, "(")))))))

# the literal-first shape, its head read: the end, after the argument
def at_b.go(ok: Bool, r5: List<&2, Lex.Tok>, +lit: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      tail_b(skip(r5, SGo{0n}, []), lit)
    case False{}:
      None{}

# a token of kind k0 and text t0, then these: the literal-first shape?
def at_b(k0: Lex.TokKind, +t0: String, toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Con{Lex.Tok{k1, +t1, l1, c1}, Con{Lex.Tok{k2, +t2, l2, c2}, Con{Lex.Tok{k3, +t3, l3, c3},
      Con{Lex.Tok{k4, +t4, l4, c4}, Con{Lex.Tok{k5, +t5, l5, c5}, r5}}}}}:
      at_b.go(head_b(k0, t0, t1, k2, t3, t4, t5), r5, t2)
    case other:
      None{}

# the first message, else the second
def either(ma: Maybe<&2, String>, mb: Maybe<&2, String>) -> Maybe<&2, String>:
  match ma:
    case None{}:
      mb
    case Some{x}:
      Some{x}

# a token of kind k0 and text t0, then these: either shape? what the finding
# says when they make one
def at(+k0: Lex.TokKind, +t0: String, +toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  either(at_a(k0, t0, toks), at_b(k0, t0, toks))

# the finding a run makes, if any, before the rest
def hit(m: Maybe<&2, String>, +path: String, +l: U32, +c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match m:
    case None{}:
      more
    case Some{msg}:
      F.Finding{path, l, c, 9, "prefix", msg} <> more

# every run of either shape among the tokens, in order
def walk(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      hit(at(k, t, rest), path, l, c, walk(rest, path))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path))

# the rule, told the file's role (src/role.bend): a law or proof file is
# skipped
def check.role(r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Role.is_law_file(r), [], _u => walk(T.sig(toks), path))
