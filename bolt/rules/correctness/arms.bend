# rule arms: a Nat arm no value can reach. `case kn+p:` matches every Nat
# from k up, so a later `case jn+q:` with j >= k, or a later `case mn:` with
# m >= k, never runs. The checker accepts it and the match quietly returns
# the earlier arm (nohzafk pat_bad: 0n, 1n+p, 2n+p gives f(2n) = 1; bend
# 2.0.16 still does). Put the narrower arms first: the literals, then the
# larger n+p. `Succ{p}` and `Succ{_}` count as 1n+p. Only a
# single-scrutinee match is read: a column of a multi-scrutinee match is
# skipped.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../lazy/lazy.bend as Lazy
import ../tokens.bend as T

# what an arm matches: from k up (text is its pattern), exactly k, or other
type Arm is Data:
  APlus{k: U32, text: String, line: U32, col: U32, len: U32}
  ALit{k: U32, line: U32, col: U32, len: U32}
  AOther{}

# the widest n+p arm so far: its k and its pattern
type Wide is Data:
  Wide{k: U32, text: String}

# `kn+p:` or `kn:`
def lit.shape(rest: Tree.Node, +kk: U32, +tt: String, +line: U32, +col: U32) -> Arm:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +o, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{b, +p, l2, c2}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l3, c3}}, more}}}:
      Bool.pick(Arm, String.eq(o, "+"), APlus{kk, tt ++ "+" ++ p, line, col, T.width(tt)}, AOther{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l, c}}, more}:
      ALit{kk, line, col, T.width(tt)}
    case other:
      AOther{}

# a Nat literal token's arm, once its value is read
def lit.of(mm: Maybe<&2, U32>, +tt: String, +rest: Tree.Node, +line: U32, +col: U32) -> Arm:
  match mm:
    case None{}:
      AOther{}
    case Some{+k}:
      lit.shape(rest, k, tt, line, col)

# a lone binder inside `Succ{..}`: a name or `_`
def binder(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case Lex.TWild{}:
      True{}
    case other:
      False{}

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
def widen(ww: Maybe<&2, Wide>, aa: Arm) -> Maybe<&2, Wide>:
  match ww aa:
    case None{} APlus{k, text, l, c, n}:
      Some{Wide{k, text}}
    case Some{Wide{+k, +text}} APlus{+j, +t2, l, c, n}:
      Bool.pick(Maybe<&2, Wide>, U32.is_lt(j, k), Some{Wide{j, t2}}, Some{Wide{k, text}})
    case w2 a2:
      w2

# a finding when the arm is inside the widest one above
def verdict.on(+kk: U32, +text: String, aa: Arm, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match aa:
    case APlus{+j, t, l, c, n}:
      Bool.pick(List<&2, F.Finding>, U32.is_ge(j, kk),
        F.Finding{path, l, c, n, "arms",
          "Unreachable: the case " ++ text ++ " above already matches everything from " ++ U32.show(j)
            ++ "n up; put narrower arms first."} <> more,
        more)
    case ALit{+m, l, c, n}:
      Bool.pick(List<&2, F.Finding>, U32.is_ge(m, kk),
        F.Finding{path, l, c, n, "arms",
          "Unreachable: the case " ++ text ++ " above already matches " ++ U32.show(m) ++ "n; put narrower arms first."}
          <> more,
        more)
    case AOther{}:
      more

# the arm against the widest one above, if any
def verdict(ww: Maybe<&2, Wide>, aa: Arm, +path: String, more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match ww:
    case None{}:
      more
    case Some{Wide{k, text}}:
      verdict.on(k, text, aa, path, more)

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
def walk(nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      +mine = Lazy.stop(List<&2, F.Finding>, Bool.not(single(kids)), [], _u => arms(body, None{}, path))
      List.concat(&2, F.Finding, [mine, walk(body, path), walk(rest, path)])
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  walk(tree, path)
