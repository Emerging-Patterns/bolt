# rule arms: a Nat arm no value can reach. `case kn+p:` matches every Nat
# from k up, so a later `case jn+q:` with j >= k, or a later `case mn:` with
# m >= k, never runs. The checker accepts it and the match quietly returns
# the earlier arm (with arms 0n, 1n+p, 2n+p, f(2n) is 1). Put the narrower
# arms first: the literals, then the
# larger n+p. `Succ{p}` and `Succ{_}` count as 1n+p. Only a
# single-scrutinee match is read: a column of a multi-scrutinee match is
# skipped.
#
# The same holds past Nat (`cover`, below): the checker takes any arm an
# earlier arm of its match already matches, and the match quietly answers
# with the earlier one. A lone binder (`case other:`) above a constructor
# arm, the same literal twice (`case 139:` in a table of opcodes), and two
# arms of one shape under different names (two six-item list patterns, each
# meant for its own mode) all check and run. An earlier arm covers a later
# one when their patterns read the same part for part, save that a binder of
# the earlier (a plain name or `_`) stands for a whole item of the later: a
# binder, a literal, a constructor with its `{..}`, a group, a `kn+` and
# what it adds to, and, when no `<>` follows the binder, every `<> item`
# after that one too. A match of any number of scrutinees is read, column by
# column. An arm the Nat check above reports is not reported again. What is
# not understood is not judged: a string literal is never the same as
# another (what a string says is not code), and any other operator, an angle
# bracket or a keyword inside a pattern covers nothing and is covered only
# inside an item a binder stands for; and a pattern that wraps onto the next
# line, which the tree holds only in part, is not read at all (36-item list
# patterns, each cut at the same `<>`, would else read alike).
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../lazy/lazy.bend as Lazy
import ../tokens.bend as T

# what an arm matches: from k up (text is its pattern), exactly k, or other
type Arm is Data:
  APlus{k: U32, text: String, line: U32, col: U32, len: U32}
  ALit{k: U32, line: U32, col: U32, len: U32}
  AOther{}

# the widest n+p arm so far: its k and its pattern
type Wide is Data:
  Wide{k: U32, text: String}

# a lone binder, inside `Succ{..}` or after `kn+`: a name or `_`
def binder(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TName{}:
      True{}
    case Lex.TWild{}:
      True{}
    case other:
      False{}

# `kn+p:` (p a name or `_`) or `kn:`
def lit.shape(rest: Tree.Node, +k: U32, +t: String, +line: U32, +col: U32) -> Arm:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +o, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{b, +p, l2, c2}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l3, c3}}, more}}}:
      Bool.pick(Arm, Bool.and(String.eq(o, "+"), binder(b)), APlus{k, t ++ "+" ++ p, line, col,
        T.width(t)}, AOther{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l, c}}, more}:
      ALit{k, line, col, T.width(t)}
    case other:
      AOther{}

# a Nat literal token's arm, once its value is read
def lit.of(m: Maybe<&2, U32>, +t: String, +rest: Tree.Node, +line: U32, +col: U32) -> Arm:
  match m:
    case None{}:
      AOther{}
    case Some{+k}:
      lit.shape(rest, k, t, line, col)

# a case pattern's arm
def arm(pat: Tree.Node) -> Arm:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, rest}:
      lit.of(T.nat_value(t), t, rest, l, c)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, +p, l2, c2}}, Tree.NNil{}}, close},
          more}}:
      Bool.pick(Arm, Bool.and(String.eq(t, "Succ"), binder(k)), APlus{1, "Succ{" ++ p ++ "}", l, c, 4}, AOther{})
    case other:
      AOther{}

# the widest n+p arm after this one
def widen(w: Maybe<&2, Wide>, a: Arm) -> Maybe<&2, Wide>:
  match w a:
    case None{} APlus{k, text, l, c, n}:
      Some{Wide{k, text}}
    case Some{Wide{+k, +text}} APlus{+j, +t2, l, c, n}:
      Bool.pick(Maybe<&2, Wide>, U32.is_lt(j, k), Some{Wide{j, t2}}, Some{Wide{k, text}})
    case w2 a2:
      w2

# a finding when the arm is inside the widest one above
def verdict.on(+k: U32, +text: String, a: Arm, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match a:
    case APlus{+j, t, l, c, n}:
      Bool.pick(List<&2, F.Finding>, U32.is_ge(j, k),
        F.Finding{path, l, c, n, "arms",
          "Unreachable: the case " ++ text ++ " above already matches everything from " ++ U32.show(j)
            ++ "n up; put narrower arms first."} <> more,
        more)
    case ALit{+m, l, c, n}:
      Bool.pick(List<&2, F.Finding>, U32.is_ge(m, k),
        F.Finding{path, l, c, n, "arms",
          "Unreachable: the case " ++ text ++ " above already matches " ++ U32.show(m) ++ "n; put narrower arms first."}
          <> more,
        more)
    case AOther{}:
      more

# the arm against the widest one above, if any
def verdict(w: Maybe<&2, Wide>, a: Arm, +path: String, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match w:
    case None{}:
      more
    case Some{Wide{k, text}}:
      verdict.on(k, text, a, path, more)

# a match's arms in order, against the widest n+p arm above each
def arms(body: Tree.Node, +wide: Maybe<&2, Wide>, +path: String) -> List<&2, F.Finding>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +a = arm(T.pattern(kids))
      verdict(wide, a, path, arms(rest, widen(wide, a), path))
    case Tree.NCons{h, rest}:
      arms(rest, wide, path)
    case other:
      Nil{}

# `match x:`: one scrutinee
def single(kids: Tree.Node) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +t, l, c}},
        Tree.NCons{x, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l2, c2}}, Tree.NNil{}}}}:
      String.eq(t, "match")
    case other:
      False{}

# every statement, at any depth; a single-scrutinee match's arms are read
def walk(n: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      +mine = Lazy.stop(List<&2, F.Finding>, Bool.not(single(kids)), [], _u => arms(body, None{}, path))
      List.concat(&2, F.Finding, [mine, walk(body, path), walk(rest, path)])
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  walk(tree, path)

# covered arms
# ------------

# one part of a pattern, as the cover check reads it: a binder; a word (a
# constructor's name, or a number or char literal), the same as another only
# by its text; `kn+`, which adds to the item after it; a string literal, the
# same as nothing; a bracket; a comma; `<>`; and anything else, which is
# not understood
type Part is Data:
  PAny{}
  PWord{text: String}
  PPlus{text: String}
  PStr{}
  POpen{text: String}
  PClose{text: String}
  PComma{}
  PCons{}
  PBad{}

# a pattern's nodes up to the `:` that ends it, an inline body left out
def cut(pat: Tree.Node) -> Tree.Node:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}:
      Tree.NNil{}
    case Tree.NCons{h, rest}:
      Tree.NCons{h, cut(rest)}
    case other:
      Tree.NNil{}

# does the pattern end among its own nodes, at a `:`? One that wraps onto
# the next line does not: its last part is a child statement in the tree
def ended(pat: Tree.Node) -> Bool:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      ended(rest)
    case other:
      False{}

# do the tokens open with this text, as a token of the kind wanted?
def opens.as(want: Bool, +t: String, +text: String) -> Bool:
  Bool.and(want, String.eq(t, text))

# is it a bracket that opens a group?
def opens.open(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TOpen{}:
      True{}
    case other:
      False{}

# is it an operator?
def opens.op(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TOp{}:
      True{}
    case other:
      False{}

# do the tokens open with `{`?
def opens.brace(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, t, l, c}, rest}:
      opens.as(opens.open(k), t, "{")
    case other:
      False{}

# do the tokens open with the operator `+`?
def opens.plus(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, t, l, c}, rest}:
      opens.as(opens.op(k), t, "+")
    case other:
      False{}

# an opening bracket's part: `(`, `[` or `{`; an angle bracket is not read
def part.open(+t: String) -> Part:
  Bool.pick(Part, Bool.or(String.eq(t, "("), Bool.or(String.eq(t, "["), String.eq(t, "{"))), POpen{t}, PBad{})

# an operator's part before the parts after it: `<>` is itself, `+` (a
# quantity mark, or the plus of `kn+`, which the number reads) is nothing,
# and any other is not understood
def part.op(+t: String, +more: List<&2, Part>) -> List<&2, Part>:
  Bool.pick(List<&2, Part>, String.eq(t, "+"), more,
    Bool.pick(Part, String.eq(t, "<>"), PCons{}, PBad{}) <> more)

# a token's part before the parts after it. brace: a `{` follows it (a
# plain name is then a constructor); plus: a `+` does (a number is then
# `kn+`)
def part(k: Lex.TokKind, +text: String, brace: Bool, plus: Bool, more: List<&2, Part>) -> List<&2, Part>:
  match k:
    case Lex.TName{}:
      Bool.pick(Part, brace, PWord{text}, PAny{}) <> more
    case Lex.TWild{}:
      PAny{} <> more
    case Lex.TUpper{}:
      PWord{text} <> more
    case Lex.TDotted{}:
      PWord{text} <> more
    case Lex.TNum{}:
      Bool.pick(Part, plus, PPlus{text}, PWord{text}) <> more
    case Lex.TChar{}:
      PWord{text} <> more
    case Lex.TStr{}:
      PStr{} <> more
    case Lex.TOpen{}:
      part.open(text) <> more
    case Lex.TClose{}:
      PClose{text} <> more
    case Lex.TComma{}:
      PComma{} <> more
    case Lex.TOp{}:
      part.op(text, more)
    case other:
      PBad{} <> more

# a pattern's tokens as parts, in order
def parts(toks: List<&2, Lex.Tok>) -> List<&2, Part>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, t, l, c}, +rest}:
      part(k, t, opens.brace(rest), opens.plus(rest), parts(rest))

def read.on(ok: Bool, pat: Tree.Node) -> List<&2, Part>:
  match ok:
    case True{}:
      parts(Tree.leaves(cut(pat)))
    case False{}:
      [PBad{}]

# a case pattern's parts: its tokens up to the `:` that ends it, read; one
# part that is not understood when it has no `:` (it wraps onto the next
# line), so a pattern read only in part is never judged
def read(+pat: Tree.Node) -> List<&2, Part>:
  read.on(ended(pat), pat)

# where a walk over one item of a pattern is: an item starts here; one just
# ended; a word just ended, whose `{..}` may follow; inside brackets, this
# many deep past the first; or the parts were no item
type Skip is Data:
  SWant{}
  SGot{}
  SWord{}
  SIn{depth: Nat}
  SFail{}

# where the walk is after the part an item starts with
def skip.want(pb: Part) -> Skip:
  match pb:
    case PAny{}:
      SGot{}
    case PWord{t}:
      SWord{}
    case PPlus{t}:
      SWant{}
    case PStr{}:
      SGot{}
    case POpen{t}:
      SIn{0n}
    case other:
      SFail{}

# where the walk is after a closing bracket this deep
def skip.close(d: Nat) -> Skip:
  match d:
    case 0n:
      SGot{}
    case 1n+p:
      SIn{p}

# where the walk is after a part inside brackets this deep
def skip.in(pb: Part, d: Nat) -> Skip:
  match pb:
    case POpen{t}:
      SIn{1n+d}
    case PClose{t}:
      skip.close(d)
    case other:
      SIn{d}

# the parts left once one item is walked over, and, when chain says so,
# every `<> item` after it; none when the parts open with no item
def skip(pb: List<&2, Part>, st: Skip, chain: Bool) -> Maybe<&2, List<&2, Part>>:
  match pb st chain:
    case rest SFail{} c:
      None{}
    case Nil{} SGot{} c:
      Some{Nil{}}
    case Nil{} SWord{} c:
      Some{Nil{}}
    case Nil{} other c:
      None{}
    case Con{b, rest} SWant{} c:
      skip(rest, skip.want(b), c)
    case Con{b, rest} SIn{d} c:
      skip(rest, skip.in(b, d), c)
    case Con{POpen{t}, rest} SWord{} c:
      skip(rest, SIn{0n}, c)
    case Con{PCons{}, rest} SGot{} True{}:
      skip(rest, SWant{}, True{})
    case Con{PCons{}, rest} SWord{} True{}:
      skip(rest, SWant{}, True{})
    case Con{b, rest} other c:
      Some{b <> rest}

# the parts, when the two texts are the same
def step.same(+ta: String, +tb: String, rest: List<&2, Part>) -> Maybe<&2, List<&2, Part>>:
  Bool.pick(Maybe<&2, List<&2, Part>>, String.eq(ta, tb), Some{rest}, None{})

# what is left of a later pattern once one part of an earlier one is read
# against it: a binder walks over an item (and the `<> item`s after it
# unless one is true: a `<>` follows the binder); any other part takes the
# same part; none when the later pattern has neither
def step(pa: Part, one: Bool, pb: List<&2, Part>) -> Maybe<&2, List<&2, Part>>:
  match pa pb:
    case PAny{} rest:
      skip(rest, SWant{}, Bool.not(one))
    case PWord{ta} Con{PWord{tb}, rest}:
      step.same(ta, tb, rest)
    case PPlus{ta} Con{PPlus{tb}, rest}:
      step.same(ta, tb, rest)
    case POpen{ta} Con{POpen{tb}, rest}:
      step.same(ta, tb, rest)
    case PClose{ta} Con{PClose{tb}, rest}:
      step.same(ta, tb, rest)
    case PComma{} Con{PComma{}, rest}:
      Some{rest}
    case PCons{} Con{PCons{}, rest}:
      Some{rest}
    case other rest:
      None{}

# do the parts open with `<>`?
def consed(ps: List<&2, Part>) -> Bool:
  match ps:
    case Con{PCons{}, rest}:
      True{}
    case other:
      False{}

# does an earlier pattern cover a later one? pb: what is left of the later,
# none once the earlier could not go on
def covers(pa: List<&2, Part>, pb: Maybe<&2, List<&2, Part>>) -> Bool:
  match pa pb:
    case rest None{}:
      False{}
    case Nil{} Some{left}:
      List.is_empty(&2, Part, left)
    case Con{a, +more} Some{left}:
      covers(more, step(a, consed(more), left))

# an arm above: its line and its pattern's parts
type Seen is Data:
  Seen{line: U32, parts: List<&2, Part>}

# the line of the nearest arm above whose pattern covers these parts, if
# any. hit carries whether the last one read did, at its line
def above(seen: List<&2, Seen>, +pb: List<&2, Part>, hit: Bool, +at: U32) -> Maybe<&2, U32>:
  match seen hit:
    case rest True{}:
      Some{at}
    case Nil{} False{}:
      None{}
    case Con{Seen{+line, parts}, rest} False{}:
      above(rest, pb, covers(parts, Some{pb}), line)

# does the Nat check report the arm against the widest n+p arm above it?
def told(w: Maybe<&2, Wide>, a: Arm) -> Bool:
  match w a:
    case None{} a2:
      False{}
    case Some{Wide{k, text}} APlus{j, t, l, c, n}:
      U32.is_ge(j, k)
    case Some{Wide{k, text}} ALit{m, l, c, n}:
      U32.is_ge(m, k)
    case Some{w2} AOther{}:
      False{}

# the finding a covered arm makes, if any, before the rest
def cover.hit(m: Maybe<&2, U32>, +path: String, l: U32, c: U32, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match m:
    case None{}:
      more
    case Some{line}:
      F.Finding{path, l, c, 0, "arms",
        "Unreachable: the case on line " ++ U32.show((line + 1 : U32))
          ++ " already matches everything this one does; delete this arm, or move it above that one."} <> more

# the line of the arm above that covers this one, unless the Nat check
# reports it
def cover.find(skip: Bool, +seen: List<&2, Seen>, +ps: List<&2, Part>) -> Maybe<&2, U32>:
  match skip:
    case True{}:
      None{}
    case False{}:
      above(seen, ps, False{}, 0)

# a match's arms in order, each against the arms above it. nat: the match
# has one scrutinee, so the Nat check reads it, wide its widest n+p arm so far
def cover.arms(
  body: Tree.Node,
  +seen: List<&2, Seen>,
  +wide: Maybe<&2, Wide>,
  +nat: Bool,
  +path: String
) -> List<&2, F.Finding>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +pat = T.pattern(kids)
      +ps = read(pat)
      +a = arm(pat)
      cover.hit(cover.find(Bool.and(nat, told(wide, a)), seen, ps), path, Tree.line(pat), Tree.col(pat),
        cover.arms(rest, Seen{Tree.line(pat), ps} <> seen, widen(wide, a), nat, path))
    case Tree.NCons{h, rest}:
      cover.arms(rest, seen, wide, nat, path)
    case other:
      Nil{}

# every statement, at any depth; a match's arms are read
def cover.walk(n: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      +mine = Lazy.stop(List<&2, F.Finding>, Bool.not(T.keyword(kids, "match")), [],
        _u => cover.arms(body, [], None{}, single(kids), path))
      List.concat(&2, F.Finding, [mine, cover.walk(body, path), cover.walk(rest, path)])
    case Tree.NCons{h, rest}:
      cover.walk(rest, path)
    case other:
      Nil{}

# a token's text where it is code: what a string literal or a comment says
# is left out
def blank.text(k: Lex.TokKind, t: String) -> String:
  match k:
    case Lex.TStr{}:
      ""
    case Lex.TComment{}:
      ""
    case other:
      t

# a token with what it says left out when it is a string or a comment
def blank.tok(tk: Lex.Tok) -> Lex.Tok:
  match tk:
    case Lex.Tok{+k, t, l, c}:
      Lex.Tok{k, blank.text(k, t), l, c}

# a tree with each leaf read that way: what the cover check reads, so what
# a string says can never change what it finds
def blank(n: Tree.Node) -> Tree.Node:
  match n:
    case Tree.Leaf{tok}:
      Tree.Leaf{blank.tok(tok)}
    case Tree.Group{open, kids, close}:
      Tree.Group{open, blank(kids), close}
    case Tree.Stmt{kind, kids, body}:
      Tree.Stmt{kind, blank(kids), blank(body)}
    case Tree.NNil{}:
      Tree.NNil{}
    case Tree.NCons{h, t}:
      Tree.NCons{blank(h), blank(t)}

# the rule's second check: an arm an earlier arm of its match covers
def cover(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  cover.walk(blank(tree), path)
