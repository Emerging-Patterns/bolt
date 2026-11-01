# rule empty: a length compared to zero when the value is kept. Among the
# significant tokens (spaces, newlines and comments dropped): a `(`, `[`,
# `{` or `,`, then a dotted `Nat.is_eq`, `(`, and either a dotted
# `List.length`, `(`, any tokens up to its matching `)` whose last two are a
# `,` and a plain name x, or a dotted `String.length`, `(`, a plain name x
# and `)`; then `,`, `0n` and `)`; and x again, as a plain name, among the
# tokens after that `)` and before the bracket that closes the group the
# test sits in (brackets opened on the way are skipped over, not ended on).
# One finding, on the `Nat.is_eq` token, for each such test.
# Base's List.length and String.length count every cell (and are not tail
# calls); List.is_empty and String.is_empty, which take the same arguments,
# look at one and give the same Bool. The second read is what makes the fix
# pay on both lanes: x is kept past the test, so the test's own reference is
# dropped by a count, never by freeing x. Where the test is x's last use,
# the native lane frees the cells the walk would have, and freeing a list
# the program never walked costs more than walking it (bend 2.0.38: a
# 0-1000 char String tested then dropped ran 0.27x as fast as a length,
# kept 1.57x; JS 1.65x and 1.31x), so a test with no read after it in its
# group, a test outside any group, and a read before the test are left
# alone. A LAWS.bend or a PROOF.bend, which never runs, is exempt, and so
# is a `law` and a def that is a proof (no type, `def f(x):`, or one that
# returns `-> {..}`) in any file, from its keyword to the next `def`, `type`
# or `import`. A comment is never read, and a string literal is one token
# that is no name.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# which length a test takes: a list's, a String's, or neither
type Form is Data:
  FList{}
  FStr{}
  FNone{}

# what the last tokens of a List.length's arguments were: a comma, a plain
# name right after a comma, or anything else
type Last is Data:
  LComma{}
  LName{name: String}
  LOther{}

# the name a test takes the length of, and the tokens after its `)`
type Taken is Data:
  Taken{name: String, rest: List<&2, Lex.Tok>}

# where a finding goes and what it says
type Hit is Data:
  Hit{line: U32, col: U32, msg: String}

# a bracket that opens a group, or a comma inside one: what may stand right
# before a test
def opener(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TOpen{}:
      True{}
    case Lex.TComma{}:
      True{}
    case other:
      False{}

# a token's text where it is code: a string literal or a comment says
# nothing the rule reads
def code(kk: Lex.TokKind, tt: String) -> String:
  match kk:
    case Lex.TStr{}:
      ""
    case Lex.TComment{}:
      ""
    case other:
      tt

# a dotted name
def dotted(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# a plain name
def plain(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case other:
      False{}

# the length a dotted name takes
def form(+tt: String) -> Form:
  Bool.pick(Form, String.eq(tt, "List.length"), FList{}, Bool.pick(Form, String.eq(tt, "String.length"), FStr{}, FNone{}))

# an opener, `Nat.is_eq`, `(`, a dotted name and `(`?
def head(
  k0: Lex.TokKind,
  +k1: Lex.TokKind,
  +t1: String,
  k2: Lex.TokKind,
  +t2: String,
  +k3: Lex.TokKind,
  k4: Lex.TokKind,
  +t4: String
) -> Bool:
  Bool.and(opener(k0), Bool.and(dotted(k1), Bool.and(dotted(k3), Bool.and(String.eq(code(k1, t1), "Nat.is_eq"),
    Bool.and(String.eq(code(k2, t2), "("), String.eq(code(k4, t4), "("))))))

# what a token leaves of the last tokens: a comma, a name after a comma, or
# anything else
def last.step(+kk: Lex.TokKind, +tt: String, ll: Last) -> Last:
  match kk:
    case Lex.TComma{}:
      LComma{}
    case Lex.TName{}:
      match ll:
        case LComma{}:
          LName{code(kk, tt)}
        case other:
          LOther{}
    case other:
      LOther{}

# the name a List.length's arguments end in, when the last two were a comma
# and a plain name
def last.name(ll: Last, rest: List<&2, Lex.Tok>) -> Maybe<&2, Taken>:
  match ll:
    case LName{nn}:
      Some{Taken{nn, rest}}
    case other:
      None{}

# a bracket at the depth: the length's own `)` at depth zero; else the depth
# it leaves
def close.depth(kk: Lex.TokKind, dd: Nat) -> Nat:
  match kk:
    case Lex.TOpen{}:
      1n+dd
    case Lex.TClose{}:
      match dd:
        case 0n:
          0n
        case 1n+p:
          p
    case other:
      dd

# is the token the bracket that closes the arguments, at depth zero?
def close.here(kk: Lex.TokKind, dd: Nat) -> Bool:
  match kk:
    case Lex.TClose{}:
      match dd:
        case 0n:
          True{}
        case 1n+p:
          False{}
    case other:
      False{}

# a List.length's arguments, scanned to the `)` that closes them: the name
# they end in and the tokens after that `)`; none when they end otherwise
# or run out. done carries whether the last token read was that `)`.
def close.list(toks: List<&2, Lex.Tok>, +dd: Nat, +ll: Last, done: Bool, got: Maybe<&2, Taken>) -> Maybe<&2, Taken>:
  match toks:
    case Nil{}:
      got
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      match done:
        case True{}:
          got
        case False{}:
          +here = close.here(k, dd)
          close.list(rest, close.depth(k, dd), last.step(k, t, ll), here, Bool.pick(Maybe<&2, Taken>, here,
            last.name(ll, rest), None{}))

# a String.length's argument: a plain name and `)`, then the tokens after
def close.str(toks: List<&2, Lex.Tok>) -> Maybe<&2, Taken>:
  match toks:
    case Con{Lex.Tok{+k1, +t1, l1, c1}, Con{Lex.Tok{k2, +t2, l2, c2}, rest}}:
      Bool.pick(Maybe<&2, Taken>, Bool.and(plain(k1), String.eq(code(k2, t2), ")")), Some{Taken{code(k1, t1), rest}},
        None{})
    case other:
      None{}

# the length's argument, by its form
def taken(fm: Form, +toks: List<&2, Lex.Tok>) -> Maybe<&2, Taken>:
  match fm:
    case FList{}:
      close.list(toks, 0n, LOther{}, False{}, None{})
    case FStr{}:
      close.str(toks)
    case FNone{}:
      None{}

# a plain name with x's text?
def same(+kk: Lex.TokKind, +tt: String, +xx: String) -> Bool:
  Bool.and(plain(kk), String.eq(code(kk, tt), xx))

# is x read among the tokens before the bracket that closes the group they
# sit in? found carries whether the last token read was x, live whether that
# bracket is still ahead
def kept(toks: List<&2, Lex.Tok>, +xx: String, +dd: Nat, found: Bool, live: Bool) -> Bool:
  match toks:
    case Nil{}:
      found
    case Con{Lex.Tok{+k, +t, l, c}, rest}:
      match found:
        case True{}:
          True{}
        case False{}:
          match live:
            case False{}:
              False{}
            case True{}:
              kept(rest, xx, close.depth(k, dd), same(k, t, xx), Bool.not(close.here(k, dd)))

# what a finding says: the test, its fix and why
def say(fm: Form, +xx: String) -> String:
  match fm:
    case FList{}:
      "Nat.is_eq(List.length(.., " ++ xx ++ "), 0n) counts every cell of " ++ xx ++ ", which is read again; List.is_empty(.., "
        ++ xx ++ ") looks at one and gives the same answer."
    case other:
      "Nat.is_eq(String.length(" ++ xx ++ "), 0n) counts every char of " ++ xx ++ ", which is read again; String.is_empty("
        ++ xx ++ ") looks at one and gives the same answer."

# a finding, if the test is whole and x kept
def tail.go(ok: Bool, fm: Form, xx: String, ll: U32, cc: U32) -> Maybe<&2, Hit>:
  match ok:
    case True{}:
      Some{Hit{ll, cc, say(fm, xx)}}
    case False{}:
      None{}

# the test's end, `,`, `0n` and `)`, then x kept: the finding, if any
def tail(mm: Maybe<&2, Taken>, +fm: Form, +ll: U32, +cc: U32) -> Maybe<&2, Hit>:
  match mm:
    case None{}:
      None{}
    case Some{Taken{+xx, r}}:
      match r:
        case Con{Lex.Tok{k1, +t1, l1, c1}, Con{Lex.Tok{k2, +t2, l2, c2}, Con{Lex.Tok{k3, +t3, l3, c3}, rest}}}:
          tail.go(Bool.and(String.eq(code(k1, t1), ","), Bool.and(String.eq(code(k2, t2), "0n"),
            Bool.and(String.eq(code(k3, t3), ")"),
            kept(rest, xx, 0n, False{}, True{})))), fm, xx, ll, cc)
        case other:
          None{}

# the test, its head read: the finding, if any
def at.go(ok: Bool, +fm: Form, +ll: U32, +cc: U32, r4: List<&2, Lex.Tok>) -> Maybe<&2, Hit>:
  match ok:
    case True{}:
      tail(taken(fm, r4), fm, ll, cc)
    case False{}:
      None{}

# a token of kind k0, then these: a kept test?
def at(k0: Lex.TokKind, toks: List<&2, Lex.Tok>) -> Maybe<&2, Hit>:
  match toks:
    case Con{Lex.Tok{k1, +t1, +l1, +c1}, Con{Lex.Tok{k2, +t2, l2, c2}, Con{Lex.Tok{+k3, +t3, l3, c3},
      Con{Lex.Tok{k4, +t4, l4, c4}, r4}}}}:
      at.go(head(k0, k1, t1, k2, t2, k3, k4, t4), form(code(k3, t3)), l1, c1, r4)
    case other:
      None{}

# the finding a test makes, if any, before the rest
def hit(mm: Maybe<&2, Hit>, +path: String, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      more
    case Some{Hit{ll, cc, msg}}:
      F.Finding{path, ll, cc, 9, "empty", msg} <> more

# what the two tokens after a def's parameters say: a `:` (no type: the
# def fills a law) or `->` then `{` (it returns a proof)
def proofy.head(k1: Lex.TokKind, +k2: Lex.TokKind, +t2: String) -> Bool:
  match k1:
    case Lex.TColon{}:
      True{}
    case Lex.TArrow{}:
      String.eq(code(k2, t2), "{")
    case other:
      False{}

# what a def's header says once its parameters close
def proofy.end(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k1, t1, l1, c1}, Con{Lex.Tok{k2, t2, l2, c2}, rest}}:
      proofy.head(k1, k2, t2)
    case Con{Lex.Tok{k1, t1, l1, c1}, Nil{}}:
      proofy.head(k1, Lex.TSpace{}, "")
    case other:
      False{}

# does the token close the parameters: a bracket closing at depth one?
def proofy.fin(kk: Lex.TokKind, dd: Nat) -> Bool:
  match kk:
    case Lex.TClose{}:
      match dd:
        case 1n:
          True{}
        case other:
          False{}
    case other:
      False{}

# is the def these tokens head (after `def`) a proof? Its tokens are read to
# the bracket that closes its parameters, at depth zero; fin carries whether
# the last token read was that bracket
def proofy(toks: List<&2, Lex.Tok>, +dd: Nat, fin: Bool) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{+k, t, l, c}, +rest}:
      match fin:
        case True{}:
          proofy.end(Lex.Tok{k, t, l, c} <> rest)
        case False{}:
          proofy(rest, close.depth(k, dd), proofy.fin(k, dd))

# what is skipped after a token that is no def: inside a law, from `law` on;
# code again from `type` or `import`; else as before
def item.other(+word: String, skip: Bool) -> Bool:
  Bool.pick(Bool, String.eq(word, "law"), True{}, Bool.pick(Bool, Bool.or(String.eq(word, "type"),
    String.eq(word, "import")), False{}, skip))

# what is skipped after a keyword: a def is skipped when it is a proof
def item.word(isdef: Bool, +word: String, rest: List<&2, Lex.Tok>, skip: Bool) -> Bool:
  match isdef:
    case True{}:
      proofy(rest, 0n, False{})
    case False{}:
      item.other(word, skip)

# what is skipped after a token: a law, and a def that is a proof, never run
def item(+kk: Lex.TokKind, +tt: String, rest: List<&2, Lex.Tok>, skip: Bool) -> Bool:
  match kk:
    case Lex.TKey{}:
      item.word(String.eq(code(kk, tt), "def"), code(kk, tt), rest, skip)
    case other:
      skip

# the kept test a token opens, if any, outside what is skipped
def found(skip: Bool, kk: Lex.TokKind, rest: List<&2, Lex.Tok>) -> Maybe<&2, Hit>:
  match skip:
    case True{}:
      None{}
    case False{}:
      at(kk, rest)

# every kept test among the tokens, in order; skip says whether the tokens
# so far sit in a law or a def that is a proof
def walk(toks: List<&2, Lex.Tok>, +path: String, skip: Bool) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +sk = item(k, t, rest, skip)
      hit(found(sk, k, rest), path, walk(rest, path, sk))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path, False{}))

# the rule, told the file's role (src/role.bend): a law or proof file is
# skipped
def check.role(rr: Role.Role, ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Role.is_law_file(rr), [], _u => walk(T.sig(toks), path, False{}))
